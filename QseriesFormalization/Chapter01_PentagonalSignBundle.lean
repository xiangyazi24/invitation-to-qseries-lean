import QseriesFormalization.Chapter05_Franklin

/-!
# Chapter 1 — Pre-computed pentagonal-sign bundle for indices 0..100

This file consolidates the `decide` computations of
`QseriesFormalization.PartI.Ch04Franklin.pentagonalSign m` for `m = 0, 1, …, 100`
into a single accessible bundle so that downstream
`Chapter01_PartitionCount*.lean` files do not have to re-prove each
sign-value individually.

Each `pentagonalSign_at_N` exposes the value at index `N` as a public
theorem, allowing simple `rw` access without re-deciding.

Pentagonal numbers ≤ 100 are: 1, 2, 5, 7, 12, 15, 22, 26, 35, 40, 51, 57,
70, 77, 92, 100 (with signs alternating −1, −1, +1, +1, −1, −1, …).
-/

namespace QseriesFormalization
namespace Ch01

open QseriesFormalization.PartI.Ch04Franklin

/-! ## Per-index pentagonal sign values (0..100) -/

theorem pentagonalSign_at_0 : pentagonalSign 0 = 1 := by decide
theorem pentagonalSign_at_1 : pentagonalSign 1 = -1 := by decide
theorem pentagonalSign_at_2 : pentagonalSign 2 = -1 := by decide
theorem pentagonalSign_at_3 : pentagonalSign 3 = 0 := by decide
theorem pentagonalSign_at_4 : pentagonalSign 4 = 0 := by decide
theorem pentagonalSign_at_5 : pentagonalSign 5 = 1 := by decide
theorem pentagonalSign_at_6 : pentagonalSign 6 = 0 := by decide
theorem pentagonalSign_at_7 : pentagonalSign 7 = 1 := by decide
theorem pentagonalSign_at_8 : pentagonalSign 8 = 0 := by decide
theorem pentagonalSign_at_9 : pentagonalSign 9 = 0 := by decide
theorem pentagonalSign_at_10 : pentagonalSign 10 = 0 := by decide
theorem pentagonalSign_at_11 : pentagonalSign 11 = 0 := by decide
theorem pentagonalSign_at_12 : pentagonalSign 12 = -1 := by decide
theorem pentagonalSign_at_13 : pentagonalSign 13 = 0 := by decide
theorem pentagonalSign_at_14 : pentagonalSign 14 = 0 := by decide
theorem pentagonalSign_at_15 : pentagonalSign 15 = -1 := by decide
theorem pentagonalSign_at_16 : pentagonalSign 16 = 0 := by decide
theorem pentagonalSign_at_17 : pentagonalSign 17 = 0 := by decide
theorem pentagonalSign_at_18 : pentagonalSign 18 = 0 := by decide
theorem pentagonalSign_at_19 : pentagonalSign 19 = 0 := by decide
theorem pentagonalSign_at_20 : pentagonalSign 20 = 0 := by decide
theorem pentagonalSign_at_21 : pentagonalSign 21 = 0 := by decide
theorem pentagonalSign_at_22 : pentagonalSign 22 = 1 := by decide
theorem pentagonalSign_at_23 : pentagonalSign 23 = 0 := by decide
theorem pentagonalSign_at_24 : pentagonalSign 24 = 0 := by decide
theorem pentagonalSign_at_25 : pentagonalSign 25 = 0 := by decide
theorem pentagonalSign_at_26 : pentagonalSign 26 = 1 := by decide
theorem pentagonalSign_at_27 : pentagonalSign 27 = 0 := by decide
theorem pentagonalSign_at_28 : pentagonalSign 28 = 0 := by decide
theorem pentagonalSign_at_29 : pentagonalSign 29 = 0 := by decide
theorem pentagonalSign_at_30 : pentagonalSign 30 = 0 := by decide
theorem pentagonalSign_at_31 : pentagonalSign 31 = 0 := by decide
theorem pentagonalSign_at_32 : pentagonalSign 32 = 0 := by decide
theorem pentagonalSign_at_33 : pentagonalSign 33 = 0 := by decide
theorem pentagonalSign_at_34 : pentagonalSign 34 = 0 := by decide
theorem pentagonalSign_at_35 : pentagonalSign 35 = -1 := by decide
theorem pentagonalSign_at_36 : pentagonalSign 36 = 0 := by decide
theorem pentagonalSign_at_37 : pentagonalSign 37 = 0 := by decide
theorem pentagonalSign_at_38 : pentagonalSign 38 = 0 := by decide
theorem pentagonalSign_at_39 : pentagonalSign 39 = 0 := by decide
theorem pentagonalSign_at_40 : pentagonalSign 40 = -1 := by decide
theorem pentagonalSign_at_41 : pentagonalSign 41 = 0 := by decide
theorem pentagonalSign_at_42 : pentagonalSign 42 = 0 := by decide
theorem pentagonalSign_at_43 : pentagonalSign 43 = 0 := by decide
theorem pentagonalSign_at_44 : pentagonalSign 44 = 0 := by decide
theorem pentagonalSign_at_45 : pentagonalSign 45 = 0 := by decide
theorem pentagonalSign_at_46 : pentagonalSign 46 = 0 := by decide
theorem pentagonalSign_at_47 : pentagonalSign 47 = 0 := by decide
theorem pentagonalSign_at_48 : pentagonalSign 48 = 0 := by decide
theorem pentagonalSign_at_49 : pentagonalSign 49 = 0 := by decide
theorem pentagonalSign_at_50 : pentagonalSign 50 = 0 := by decide
theorem pentagonalSign_at_51 : pentagonalSign 51 = 1 := by decide
theorem pentagonalSign_at_52 : pentagonalSign 52 = 0 := by decide
theorem pentagonalSign_at_53 : pentagonalSign 53 = 0 := by decide
theorem pentagonalSign_at_54 : pentagonalSign 54 = 0 := by decide
theorem pentagonalSign_at_55 : pentagonalSign 55 = 0 := by decide
theorem pentagonalSign_at_56 : pentagonalSign 56 = 0 := by decide
theorem pentagonalSign_at_57 : pentagonalSign 57 = 1 := by decide
theorem pentagonalSign_at_58 : pentagonalSign 58 = 0 := by decide
theorem pentagonalSign_at_59 : pentagonalSign 59 = 0 := by decide
theorem pentagonalSign_at_60 : pentagonalSign 60 = 0 := by decide
theorem pentagonalSign_at_61 : pentagonalSign 61 = 0 := by decide
theorem pentagonalSign_at_62 : pentagonalSign 62 = 0 := by decide
theorem pentagonalSign_at_63 : pentagonalSign 63 = 0 := by decide
theorem pentagonalSign_at_64 : pentagonalSign 64 = 0 := by decide
theorem pentagonalSign_at_65 : pentagonalSign 65 = 0 := by decide
theorem pentagonalSign_at_66 : pentagonalSign 66 = 0 := by decide
theorem pentagonalSign_at_67 : pentagonalSign 67 = 0 := by decide
theorem pentagonalSign_at_68 : pentagonalSign 68 = 0 := by decide
theorem pentagonalSign_at_69 : pentagonalSign 69 = 0 := by decide
theorem pentagonalSign_at_70 : pentagonalSign 70 = -1 := by decide
theorem pentagonalSign_at_71 : pentagonalSign 71 = 0 := by decide
theorem pentagonalSign_at_72 : pentagonalSign 72 = 0 := by decide
theorem pentagonalSign_at_73 : pentagonalSign 73 = 0 := by decide
theorem pentagonalSign_at_74 : pentagonalSign 74 = 0 := by decide
theorem pentagonalSign_at_75 : pentagonalSign 75 = 0 := by decide
theorem pentagonalSign_at_76 : pentagonalSign 76 = 0 := by decide
theorem pentagonalSign_at_77 : pentagonalSign 77 = -1 := by decide
theorem pentagonalSign_at_78 : pentagonalSign 78 = 0 := by decide
theorem pentagonalSign_at_79 : pentagonalSign 79 = 0 := by decide
theorem pentagonalSign_at_80 : pentagonalSign 80 = 0 := by decide
theorem pentagonalSign_at_81 : pentagonalSign 81 = 0 := by decide
theorem pentagonalSign_at_82 : pentagonalSign 82 = 0 := by decide
theorem pentagonalSign_at_83 : pentagonalSign 83 = 0 := by decide
theorem pentagonalSign_at_84 : pentagonalSign 84 = 0 := by decide
theorem pentagonalSign_at_85 : pentagonalSign 85 = 0 := by decide
theorem pentagonalSign_at_86 : pentagonalSign 86 = 0 := by decide
theorem pentagonalSign_at_87 : pentagonalSign 87 = 0 := by decide
theorem pentagonalSign_at_88 : pentagonalSign 88 = 0 := by decide
theorem pentagonalSign_at_89 : pentagonalSign 89 = 0 := by decide
theorem pentagonalSign_at_90 : pentagonalSign 90 = 0 := by decide
theorem pentagonalSign_at_91 : pentagonalSign 91 = 0 := by decide
theorem pentagonalSign_at_92 : pentagonalSign 92 = 1 := by decide
theorem pentagonalSign_at_93 : pentagonalSign 93 = 0 := by decide
theorem pentagonalSign_at_94 : pentagonalSign 94 = 0 := by decide
theorem pentagonalSign_at_95 : pentagonalSign 95 = 0 := by decide
theorem pentagonalSign_at_96 : pentagonalSign 96 = 0 := by decide
theorem pentagonalSign_at_97 : pentagonalSign 97 = 0 := by decide
theorem pentagonalSign_at_98 : pentagonalSign 98 = 0 := by decide
theorem pentagonalSign_at_99 : pentagonalSign 99 = 0 := by decide
theorem pentagonalSign_at_100 : pentagonalSign 100 = 1 := by decide

end Ch01
end QseriesFormalization
