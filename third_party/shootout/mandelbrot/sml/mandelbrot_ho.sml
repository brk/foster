val (K, L2) = (50, 4.0)

fun out b = TextIO.output1 (TextIO.stdOut, Byte.byteToChar b)

fun enumRange32 (s, e, f) =
  if s < e then (f s; enumRange32 (s + 1, e, f)) else ()

fun mandel (h, w) =
   let fun p (x, y) =
          let val (Cr, Ci) = (real x*2.0/real w-1.5, real y*2.0/real h-1.0)
              fun lp (r, i, k) =
                  let val (r2, i2) = (r*r, i*i)
                  in r2+i2 <= L2 andalso
                     (k=0 orelse lp (r2-i2+Cr, (r+r)*i+Ci, k-1)) end
          in lp (0.0, 0.0, K) end
       fun xl (x, y, b, n) =
          if x = w then (out (Word8.<< (b, n)) ; yl (y+1))
          else let val (b, n) = if n=0w0 then (out b ; (0w0, 0w8)) else (b, n)
               in xl (x+1, y, b+b+(if p (x, y) then 0w1 else 0w0), n-0w1) end
       and yl y = if y < h then xl (0, y, 0w0, 0w8) else ()
   in app print ["P4\n", Int.toString h, " ", Int.toString w, "\n"] ; yl 0 end

val nraw = valOf (Int.fromString (hd (CommandLine.arguments ()))) handle _ => 600
val img_W_H_bits = (nraw + 7) div 8
val img_W_H = img_W_H_bits * 8
val num_pixel_bytes = img_W_H *img_W_H_bits
val pixels = Array.array (num_pixel_bytes, Word8.fromInt 0)
val initr = Array.array (img_W_H, 0.0)
val initi = Array.array (img_W_H, 0.0)

fun m () =
  let
    val _ = enumRange32 (0, img_W_H, fn xy => 
      (Array.update (initr, xy, (real xy * 2.0/real img_W_H - 1.5));
       Array.update (initi, xy, (real xy * 2.0/real img_W_H - 1.0))))

    val pgr = Array.array (8, 0.0)
    val pgi = Array.array (8, 0.0)
    val eightPixels = ref (Word8.fromInt 255)

    val  _ = enumRange32 (0, img_W_H, fn y =>
      let
       val pfi = Array.sub (initi, y)
       fun inner xMaj =
        if xMaj < img_W_H
         then
            let
              val _ = enumRange32 (0, 8, fn xMinor =>
                (Array.update (pgr, xMinor, Array.sub (initr, xMaj + xMinor));
                 Array.update (pgi, xMinor, pfi)))
              val _ = eightPixels := 0w255
              fun loop iter =
                if iter = 0 then () else
                 if (!eightPixels) = 0w0 then () else
                   (enumRange32 (0, 8, fn xMinor =>
                      let val r = Array.sub (pgr, xMinor)
                          val i = Array.sub (pgi, xMinor) in
                      ( Array.update (pgr, xMinor, (r * r) - (i * i) + Array.sub (initr, xMaj + xMinor));
                        Array.update (pgi, xMinor, (2.0 * r * i) + pfi);
                        if ((r * r) + (i * i) > L2)
                            then (let val mask = Word8.>> (0wx80, Word.fromInt xMinor) in
                                  eightPixels := Word8.andb (!eightPixels , Word8.notb mask) end)
                            else ())
                      end
                    ); loop (iter - 1))
              val _ = loop K 
              val index = (y * img_W_H_bits) + (xMaj div 8) 
              val _ = Array.update (pixels, index, !eightPixels)
            in
              inner (xMaj + 8)
            end
          else ()
     in inner 0 end
      ) in

  (List.app print ["P4\n", Int.toString img_W_H, " ", Int.toString img_W_H, "\n"];
   Array.app (fn b => (out b; ())) pixels)

  end

val _ = m ()

