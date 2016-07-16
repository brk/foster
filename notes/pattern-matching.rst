Pattern Matching
================

Pattern matching without guards can be compiled efficiently
to decision trees as described by e.g. Maranget.

I'm not sure yet how to best minimize the performance impact
of adding guards to pattern matches. If every arm has a guard,
then::
    case v
      of p1 if g1 -> e1
      of p2 if g2 -> e2
      ...
      of pn if gn -> en
    end
is faithfully encoded by the source-to-source transformation::
    case v
      of p1 -> if g1 then e1 else kont2 ! end
      of _  -> kont2 !
    end
      where
        kont2 = {
          case v
            of p2 -> if g2 then e2 else kont3 ! end
            of _  -> kont3 !
          end
            where kont3 = ...
        };
If the patterns don't contain any useful information,
we can't do significantly better in terms of what decision
tree we build.
