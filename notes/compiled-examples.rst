Compiled Code Snippets
----------------------

Until, implemented with functions and pattern matching
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

LLVM assembly for this code::

  hof-until-case = { c : {i1} => b : { () } =>
    case c ()
      of true ->  0
      of false -> b (); hof-until-case c b
    end
  };

is as follows::

  ; Function Attrs: noinline uwtable
  define internal fastcc i8 @hof-until-case({ i1 (i8*)*, i8* }* %"c!1399", { {}* (i8*)*, i8* }* %"b!1400") #24 {
  entry:
    %"alloca point" = bitcast i32 0 to i32                      ; #uses = 0	; i32
    %"br args: c!1399; b!1400;" = bitcast i32 0 to i32          ; #uses = 0	; i32
    br label %hof-until-case.L2220

  hof-until-case.L2220:               ; preds = %entry
    %"c!13991" = phi { i1 (i8*)*, i8* }* [ %"c!1399", %entry ]  ; #uses = 2	; { i1 (i8*)*, i8* }*
    %"b!14002" = phi { {}* (i8*)*, i8* }* [ %"b!1400", %entry ] ; #uses = 2	; { {}* (i8*)*, i8* }*
    br label %mustbecont_hdr.hof-until-case_.L2221

  mustbecont_hdr.hof-until-case_.L2221: ; preds = %.cont.L2229, %hof-until-case.L2220
    %getCloEnv.subgep = getelementptr { i1 (i8*)*, i8* }, { i1 (i8*)*, i8* }* %"c!13991", i32 0, i32 1 ; #uses = 1	; i8**
    %getCloEnv.subgep_ld = load i8*, i8** %getCloEnv.subgep     ; #uses = 1	; i8*
    %getCloCode.subgep = getelementptr { i1 (i8*)*, i8* }, { i1 (i8*)*, i8* }* %"c!13991", i32 0, i32 0 ; #uses = 1	; i1 (i8*)**
    %getCloCode.subgep_ld = load i1 (i8*)*, i1 (i8*)** %getCloCode.subgep ; #uses = 1	; i1 (i8*)*
    %".cr!2231" = call fastcc i1 %getCloCode.subgep_ld(i8* %getCloEnv.subgep_ld) ; #uses = 1	; i1
    %"ABOVE CALL MAY TRIGGER GC..." = bitcast i32 0 to i32      ; #uses = 0	; i32
    %"br args: .cr!2231;" = bitcast i32 0 to i32                ; #uses = 0	; i32
    br label %.cont.L2222

  .cont.L2222:                                      ; preds = %mustbecont_hdr.hof-until-case_.L2221
    %"scrut.occ!2292" = phi i1 [ %".cr!2231", %mustbecont_hdr.hof-until-case_.L2221 ] ; #uses = 1	; i1
    br label %.dt.switch.L2293

  .dt.switch.L2293:                                 ; preds = %.cont.L2222
    %"occ[.x!1495]()--" = bitcast i32 0 to i32                  ; #uses = 0	; i32
    switch i1 %"scrut.occ!2292", label %case.arm.L2227 [
      i1 true, label %case.arm.L2224
    ]

  case.arm.L2227:                                   ; preds = %.dt.switch.L2293
    %getCloEnv.subgep3 = getelementptr { {}* (i8*)*, i8* }, { {}* (i8*)*, i8* }* %"b!14002", i32 0, i32 1 ; #uses = 1	; i8**
    %getCloEnv.subgep3_ld = load i8*, i8** %getCloEnv.subgep3   ; #uses = 1	; i8*
    %getCloCode.subgep4 = getelementptr { {}* (i8*)*, i8* }, { {}* (i8*)*, i8* }* %"b!14002", i32 0, i32 0 ; #uses = 1	; {}* (i8*)**
    %getCloCode.subgep4_ld = load {}* (i8*)*, {}* (i8*)** %getCloCode.subgep4 ; #uses = 1	; {}* (i8*)*
    %".cr!2230" = call fastcc {}* %getCloCode.subgep4_ld(i8* %getCloEnv.subgep3_ld) ; #uses = 1	; {}*
    %"ABOVE CALL MAY TRIGGER GC...5" = bitcast i32 0 to i32     ; #uses = 0	; i32
    %"br args: .cr!2230;" = bitcast i32 0 to i32                ; #uses = 0	; i32
    br label %.cont.L2229

  .cont.L2229:                                      ; preds = %case.arm.L2227
    %".seq!1408" = phi {}* [ %".cr!2230", %case.arm.L2227 ]     ; #uses = 0	; {}*
    br label %mustbecont_hdr.hof-until-case_.L2221

  case.arm.L2224:                                   ; preds = %.dt.switch.L2293
    ret i8 0
  }

which gets optimized to this. Note that LLVM IR optimizations turn ``switch`` into ``br``.
Also note that the tail recursion isn't turned into a CFG loop (yet)::

  ; Function Attrs: noinline uwtable
  define internal fastcc void @hof-until-case({ i1 (i8*)*, i8* }* nocapture readonly %"c!1399",
                                              { {}* (i8*)*, i8* }* nocapture readonly %"b!1400") unnamed_addr #7 {
  entry:
    %getCloEnv.subgep = getelementptr { i1 (i8*)*, i8* }, { i1 (i8*)*, i8* }* %"c!1399", i64 0, i32 1 ; #uses = 2	; i8**
    %getCloEnv.subgep_ld1 = load i8*, i8** %getCloEnv.subgep, align 8 ; #uses = 1	; i8*
    %getCloCode.subgep = getelementptr { i1 (i8*)*, i8* }, { i1 (i8*)*, i8* }* %"c!1399", i64 0, i32 0 ; #uses = 2	; i1 (i8*)**
    %getCloCode.subgep_ld2 = load i1 (i8*)*, i1 (i8*)** %getCloCode.subgep, align 8 ; #uses = 1	; i1 (i8*)*
    %".cr!22313" = tail call fastcc i1 %getCloCode.subgep_ld2(i8* %getCloEnv.subgep_ld1) ; #uses = 1	; i1
    br i1 %".cr!22313", label %case.arm.L2224, label %case.arm.L2227.lr.ph

  case.arm.L2227.lr.ph:                             ; preds = %entry
    %getCloEnv.subgep3 = getelementptr { {}* (i8*)*, i8* }, { {}* (i8*)*, i8* }* %"b!1400", i64 0, i32 1 ; #uses = 1	; i8**
    %getCloCode.subgep4 = getelementptr { {}* (i8*)*, i8* }, { {}* (i8*)*, i8* }* %"b!1400", i64 0, i32 0 ; #uses = 1	; {}* (i8*)**
    br label %case.arm.L2227

  case.arm.L2227:                                   ; preds = %case.arm.L2227.lr.ph, %case.arm.L2227
    %getCloEnv.subgep3_ld = load i8*, i8** %getCloEnv.subgep3, align 8 ; #uses = 1	; i8*
    %getCloCode.subgep4_ld = load {}* (i8*)*, {}* (i8*)** %getCloCode.subgep4, align 8 ; #uses = 1	; {}* (i8*)*
    %".cr!2230" = tail call fastcc {}* %getCloCode.subgep4_ld(i8* %getCloEnv.subgep3_ld) ; #uses = 0	; {}*
    %getCloEnv.subgep_ld = load i8*, i8** %getCloEnv.subgep, align 8 ; #uses = 1	; i8*
    %getCloCode.subgep_ld = load i1 (i8*)*, i1 (i8*)** %getCloCode.subgep, align 8 ; #uses = 1	; i1 (i8*)*
    %".cr!2231" = tail call fastcc i1 %getCloCode.subgep_ld(i8* %getCloEnv.subgep_ld) ; #uses = 1	; i1
    br i1 %".cr!2231", label %case.arm.L2224, label %case.arm.L2227

  case.arm.L2224:                                   ; preds = %case.arm.L2227, %entry
    ret void
  }

and finally this assembly (note that the iteration is done via an assembly-level jump, not a full recursive call)::

  "hof-until-case":         # @hof-until-case
          .cfi_startproc
  # %bb.0:                                # %entry
          pushq	%rbp
          .cfi_def_cfa_offset 16
          .cfi_offset %rbp, -16
          movq	%rsp, %rbp
          .cfi_def_cfa_register %rbp
          pushq	%r14
          pushq	%rbx
          subq	$16, %rsp
          .cfi_offset %rbx, -32
          .cfi_offset %r14, -24
          movq	%rsi, %r14
          movq	%rdi, %rbx
          movq	8(%rdi), %rdi
          callq	*(%rbx)
          subq	$8, %rsp
          testb	$1, %al
          jne	.LBB9_3
          .p2align	4, 0x90
  .LBB9_1:                                # %case.arm.L2227
                                          # =>This Inner Loop Header: Depth=1
          movq	8(%r14), %rdi
          callq	*(%r14)
          subq	$8, %rsp
          movq	8(%rbx), %rdi
          callq	*(%rbx)
          subq	$8, %rsp
          testb	$1, %al
          je	.LBB9_1
  .LBB9_3:                                # %case.arm.L2224
          addq	$16, %rsp
          popq	%rbx
          popq	%r14
          popq	%rbp
          .cfi_def_cfa %rsp, 8
          retq	$8

