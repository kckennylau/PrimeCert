/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import PrimeCert.Pocklington

/-! # List of primes below 1000 -/

namespace PrimeCert

theorem prime_2 : Nat.Prime 2 := Nat.prime_two
theorem prime_3 : Nat.Prime 3 := Nat.prime_three
theorem prime_5 : Nat.Prime 5 := pock% [2, (5, 2, 2 ^ 2)]
theorem prime_7 : Nat.Prime 7 := pock% [3, (7, 2, 3)]
theorem prime_11 : Nat.Prime 11 := pock% [5, (11, 2, 5)]
theorem prime_13 : Nat.Prime 13 := pock% [2, (13, 2, 2 ^ 2)]
theorem prime_17 : Nat.Prime 17 := pock% [2, (17, 3, 2 ^ 3)]
theorem prime_19 : Nat.Prime 19 := pock% [3, (19, 2, 3 ^ 2)]
theorem prime_23 : Nat.Prime 23 := pock% [11, (23, 2, 11)]
theorem prime_29 : Nat.Prime 29 := pock% [7, (29, 2, 7)]
theorem prime_31 : Nat.Prime 31 := pock% [2, 3, (31, 3, 2 * 3)]
theorem prime_37 : Nat.Prime 37 := pock% [3, (37, 2, 3 ^ 2)]
theorem prime_41 : Nat.Prime 41 := pock% [2, (41, 3, 2 ^ 3)]
theorem prime_43 : Nat.Prime 43 := pock% [7, (43, 2, 7)]
theorem prime_47 : Nat.Prime 47 := pock% [23, (47, 2, 23)]
theorem prime_53 : Nat.Prime 53 := pock% [13, (53, 2, 13)]
theorem prime_59 : Nat.Prime 59 := pock% [29, (59, 2, 29)]
theorem prime_61 : Nat.Prime 61 := pock% [2, 3, (61, 2, 2 ^ 2 * 3)]
theorem prime_67 : Nat.Prime 67 := pock% [11, (67, 2, 11)]
theorem prime_71 : Nat.Prime 71 := pock% [2, 5, (71, 7, 2 * 5)]
theorem prime_73 : Nat.Prime 73 := pock% [3, (73, 2, 3 ^ 2)]
theorem prime_79 : Nat.Prime 79 := pock% [13, (79, 2, 13)]
theorem prime_83 : Nat.Prime 83 := pock% [41, (83, 2, 41)]
theorem prime_89 : Nat.Prime 89 := pock% [11, (89, 2, 11)]
theorem prime_97 : Nat.Prime 97 := pock% [2, (97, 5, 2 ^ 4)]

theorem prime_101 : Nat.Prime 101 := pock% [5, (101, 2, 5 ^ 2)]
theorem prime_103 : Nat.Prime 103 := pock% [17, (103, 2, 17)]
theorem prime_107 : Nat.Prime 107 := pock% [53, (107, 2, 53)]
theorem prime_109 : Nat.Prime 109 := pock% [3, (109, 3, 3 ^ 3)]
theorem prime_113 : Nat.Prime 113 := pock% [2, (113, 3, 2 ^ 4)]
theorem prime_127 : Nat.Prime 127 := pock% [2, 7, (127, 3, 2 * 7)]
theorem prime_131 : Nat.Prime 131 := pock% [13, (131, 2, 13)]
theorem prime_137 : Nat.Prime 137 := pock% [17, (137, 2, 17)]
theorem prime_139 : Nat.Prime 139 := pock% [23, (139, 2, 23)]
theorem prime_149 : Nat.Prime 149 := pock% [37, (149, 2, 37)]
theorem prime_151 : Nat.Prime 151 := pock% [5, (151, 3, 5 ^ 2)]
theorem prime_157 : Nat.Prime 157 := pock% [13, (157, 2, 13)]
theorem prime_163 : Nat.Prime 163 := pock% [3, (163, 2, 3 ^ 4)]
theorem prime_167 : Nat.Prime 167 := pock% [83, (167, 2, 83)]
theorem prime_173 : Nat.Prime 173 := pock% [43, (173, 2, 43)]
theorem prime_179 : Nat.Prime 179 := pock% [89, (179, 2, 89)]
theorem prime_181 : Nat.Prime 181 := pock% [2, 5, (181, 2, 2 ^ 2 * 5)]
theorem prime_191 : Nat.Prime 191 := pock% [19, (191, 2, 19)]
theorem prime_193 : Nat.Prime 193 := pock% [2, (193, 5, 2 ^ 6)]
theorem prime_197 : Nat.Prime 197 := pock% [7, (197, 2, 7 ^ 2)]
theorem prime_199 : Nat.Prime 199 := pock% [2, 3, (199, 3, 2 * 3 ^ 2)]

theorem prime_211 : Nat.Prime 211 := pock% [3, 5, (211, 2, 3 * 5)]
theorem prime_223 : Nat.Prime 223 := pock% [37, (223, 2, 37)]
theorem prime_227 : Nat.Prime 227 := pock% [113, (227, 2, 113)]
theorem prime_229 : Nat.Prime 229 := pock% [19, (229, 2, 19)]
theorem prime_233 : Nat.Prime 233 := pock% [29, (233, 2, 29)]
theorem prime_239 : Nat.Prime 239 := pock% [17, (239, 2, 17)]
theorem prime_241 : Nat.Prime 241 := pock% [2, (241, 7, 2 ^ 4)]
theorem prime_251 : Nat.Prime 251 := pock% [5, (251, 3, 5 ^ 3)]
theorem prime_257 : Nat.Prime 257 := pock% [2, (257, 3, 2 ^ 8)]
theorem prime_263 : Nat.Prime 263 := pock% [131, (263, 2, 131)]
theorem prime_269 : Nat.Prime 269 := pock% [67, (269, 2, 67)]
theorem prime_271 : Nat.Prime 271 := pock% [3, (271, 2, 3 ^ 3)]
theorem prime_277 : Nat.Prime 277 := pock% [23, (277, 2, 23)]
theorem prime_281 : Nat.Prime 281 := pock% [2, 5, (281, 3, 2 ^ 3 * 5)]
theorem prime_283 : Nat.Prime 283 := pock% [47, (283, 2, 47)]
theorem prime_293 : Nat.Prime 293 := pock% [73, (293, 2, 73)]

-- theorem prime_307 : Nat.Prime 307 :=
-- theorem prime_311 : Nat.Prime 311 :=
-- theorem prime_313 : Nat.Prime 313 :=
-- theorem prime_317 : Nat.Prime 317 :=
-- theorem prime_331 : Nat.Prime 331 :=
-- theorem prime_337 : Nat.Prime 337 :=
-- theorem prime_347 : Nat.Prime 347 :=
-- theorem prime_349 : Nat.Prime 349 :=
-- theorem prime_353 : Nat.Prime 353 :=
-- theorem prime_359 : Nat.Prime 359 :=
-- theorem prime_367 : Nat.Prime 367 :=
-- theorem prime_373 : Nat.Prime 373 :=
-- theorem prime_379 : Nat.Prime 379 :=
-- theorem prime_383 : Nat.Prime 383 :=
-- theorem prime_389 : Nat.Prime 389 :=
-- theorem prime_397 : Nat.Prime 397 :=

-- theorem prime_401 : Nat.Prime 401 :=
-- theorem prime_409 : Nat.Prime 409 :=
-- theorem prime_419 : Nat.Prime 419 :=
-- theorem prime_421 : Nat.Prime 421 :=
-- theorem prime_431 : Nat.Prime 431 :=
-- theorem prime_433 : Nat.Prime 433 :=
-- theorem prime_439 : Nat.Prime 439 :=
-- theorem prime_443 : Nat.Prime 443 :=
-- theorem prime_449 : Nat.Prime 449 :=
-- theorem prime_457 : Nat.Prime 457 :=
-- theorem prime_461 : Nat.Prime 461 :=
-- theorem prime_463 : Nat.Prime 463 :=
-- theorem prime_467 : Nat.Prime 467 :=
-- theorem prime_479 : Nat.Prime 479 :=
-- theorem prime_487 : Nat.Prime 487 :=
-- theorem prime_491 : Nat.Prime 491 :=
-- theorem prime_499 : Nat.Prime 499 :=

-- theorem prime_503 : Nat.Prime 503 :=
-- theorem prime_509 : Nat.Prime 509 :=
-- theorem prime_521 : Nat.Prime 521 :=
-- theorem prime_523 : Nat.Prime 523 :=
-- theorem prime_541 : Nat.Prime 541 :=
-- theorem prime_547 : Nat.Prime 547 :=
-- theorem prime_557 : Nat.Prime 557 :=
-- theorem prime_563 : Nat.Prime 563 :=
-- theorem prime_569 : Nat.Prime 569 :=
-- theorem prime_571 : Nat.Prime 571 :=
-- theorem prime_577 : Nat.Prime 577 :=
-- theorem prime_587 : Nat.Prime 587 :=
-- theorem prime_593 : Nat.Prime 593 :=
-- theorem prime_599 : Nat.Prime 599 :=

-- theorem prime_601 : Nat.Prime 601 :=
-- theorem prime_607 : Nat.Prime 607 :=
-- theorem prime_613 : Nat.Prime 613 :=
-- theorem prime_617 : Nat.Prime 617 :=
-- theorem prime_619 : Nat.Prime 619 :=
-- theorem prime_631 : Nat.Prime 631 :=
-- theorem prime_641 : Nat.Prime 641 :=
-- theorem prime_643 : Nat.Prime 643 :=
-- theorem prime_647 : Nat.Prime 647 :=
-- theorem prime_653 : Nat.Prime 653 :=
-- theorem prime_659 : Nat.Prime 659 :=
-- theorem prime_661 : Nat.Prime 661 :=
-- theorem prime_673 : Nat.Prime 673 :=
-- theorem prime_677 : Nat.Prime 677 :=
-- theorem prime_683 : Nat.Prime 683 :=
-- theorem prime_691 : Nat.Prime 691 :=

-- theorem prime_701 : Nat.Prime 701 :=
-- theorem prime_709 : Nat.Prime 709 :=
-- theorem prime_719 : Nat.Prime 719 :=
-- theorem prime_727 : Nat.Prime 727 :=
-- theorem prime_733 : Nat.Prime 733 :=
-- theorem prime_739 : Nat.Prime 739 :=
-- theorem prime_743 : Nat.Prime 743 :=
-- theorem prime_751 : Nat.Prime 751 :=
-- theorem prime_757 : Nat.Prime 757 :=
-- theorem prime_761 : Nat.Prime 761 :=
-- theorem prime_769 : Nat.Prime 769 :=
-- theorem prime_773 : Nat.Prime 773 :=
-- theorem prime_787 : Nat.Prime 787 :=
-- theorem prime_797 : Nat.Prime 797 :=

-- theorem prime_809 : Nat.Prime 809 :=
-- theorem prime_811 : Nat.Prime 811 :=
-- theorem prime_821 : Nat.Prime 821 :=
-- theorem prime_823 : Nat.Prime 823 :=
-- theorem prime_827 : Nat.Prime 827 :=
-- theorem prime_829 : Nat.Prime 829 :=
-- theorem prime_839 : Nat.Prime 839 :=
-- theorem prime_853 : Nat.Prime 853 :=
-- theorem prime_857 : Nat.Prime 857 :=
-- theorem prime_859 : Nat.Prime 859 :=
-- theorem prime_863 : Nat.Prime 863 :=
-- theorem prime_877 : Nat.Prime 877 :=
-- theorem prime_881 : Nat.Prime 881 :=
-- theorem prime_883 : Nat.Prime 883 :=
-- theorem prime_887 : Nat.Prime 887 :=

-- theorem prime_907 : Nat.Prime 907 :=
-- theorem prime_911 : Nat.Prime 911 :=
-- theorem prime_919 : Nat.Prime 919 :=
-- theorem prime_929 : Nat.Prime 929 :=
-- theorem prime_937 : Nat.Prime 937 :=
-- theorem prime_941 : Nat.Prime 941 :=
-- theorem prime_947 : Nat.Prime 947 :=
-- theorem prime_953 : Nat.Prime 953 :=
-- theorem prime_967 : Nat.Prime 967 :=
-- theorem prime_971 : Nat.Prime 971 :=
-- theorem prime_977 : Nat.Prime 977 :=
-- theorem prime_983 : Nat.Prime 983 :=
-- theorem prime_991 : Nat.Prime 991 :=
-- theorem prime_997 : Nat.Prime 997 :=

local elab "make%" a:num b:num : command => do
  for i in Array.range' a.getNat b.getNat do
    if Nat.Prime i then
      have iStx := Lean.Syntax.mkNatLit i
      have name := Lean.mkIdent <| Lean.Name.mkSimple s!"prime_{i}"
      Lean.Elab.Command.elabCommand =<< `(command| theorem $name : Nat.Prime $iStx := by norm_num)

make% 301 2000

/-- info: PrimeCert.prime_997 : Nat.Prime 997 -/
#guard_msgs in
#check prime_997

end PrimeCert
