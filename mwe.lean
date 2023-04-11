import Lean

open Lean

opaque foo : Int → Int
axiom foo.pos (x : Int) (h : x ≥ 0) : foo x =  1
axiom foo.neg (x : Int) (h : ¬(x ≥ 0)) : foo x = -1

