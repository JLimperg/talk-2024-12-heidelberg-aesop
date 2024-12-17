/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Amelia Livingston, Yury Kudryashov,
Neil Strickland, Aaron Anderson
-/
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Divisibility.Units

/-!
# Divisibility in groups with zero.

Lemmas about divisibility in groups and monoids with zero.

-/

assert_not_exists DenselyOrdered

variable {α : Type*}

section SemigroupWithZero

variable [SemigroupWithZero α] {a : α}

theorem eq_zero_of_zero_dvd (h : 0 ∣ a) : a = 0 := by
  aesop (add simp [dvd_def])

@[simp]
theorem zero_dvd_zero : Dvd.dvd (0 : α) 0 :=
  ⟨0, by aesop⟩

/-- Given an element `a` of a commutative semigroup with zero, there exists another element whose
    product with zero equals `a` iff `a` equals zero. -/
@[simp]
theorem zero_dvd_iff : 0 ∣ a ↔ a = 0 := by
  aesop (add safe destruct eq_zero_of_zero_dvd)

@[simp]
theorem dvd_zero (a : α) : a ∣ 0 :=
  Dvd.intro 0 (by simp)

end SemigroupWithZero

/-- Given two elements `b`, `c` of a `CancelMonoidWithZero` and a nonzero element `a`,
 `a*b` divides `a*c` iff `b` divides `c`. -/
theorem mul_dvd_mul_iff_left [CancelMonoidWithZero α] {a b c : α} (ha : a ≠ 0) :
    a * b ∣ a * c ↔ b ∣ c :=
  exists_congr fun d => by rw [mul_assoc, mul_right_inj' ha]

/-- Given two elements `a`, `b` of a commutative `CancelMonoidWithZero` and a nonzero
  element `c`, `a*c` divides `b*c` iff `a` divides `b`. -/
theorem mul_dvd_mul_iff_right [CancelCommMonoidWithZero α] {a b c : α} (hc : c ≠ 0) :
    a * c ∣ b * c ↔ a ∣ b :=
  exists_congr fun d => by rw [mul_right_comm, mul_left_inj' hc]

section CommMonoidWithZero

variable [CommMonoidWithZero α]

/-- `DvdNotUnit a b` expresses that `a` divides `b` "strictly", i.e. that `b` divided by `a`
is not a unit. -/
def DvdNotUnit (a b : α) : Prop :=
  a ≠ 0 ∧ ∃ x, ¬IsUnit x ∧ b = a * x

@[aesop 90%]
theorem dvdNotUnit_of_dvd_of_not_dvd {a b : α} (hd : a ∣ b) (hnd : ¬b ∣ a) : DvdNotUnit a b := by
  constructor
  · rintro rfl
    exact hnd (dvd_zero _)
  · rcases hd with ⟨c, rfl⟩
    refine ⟨c, ?_, rfl⟩
    rintro ⟨u, rfl⟩
    simp at hnd

variable {x y : α}

theorem isRelPrime_zero_left : IsRelPrime 0 x ↔ IsUnit x :=
  ⟨(· (dvd_zero _) dvd_rfl), IsUnit.isRelPrime_right⟩

@[aesop safe forward]
theorem isRelPrime_zero_left₁ : IsRelPrime 0 x → IsUnit x :=
  isRelPrime_zero_left.mp

@[aesop safe forward]
theorem isRelPrime_zero_left₂ : IsUnit x → IsRelPrime 0 x :=
  isRelPrime_zero_left.mpr

theorem isRelPrime_zero_right : IsRelPrime x 0 ↔ IsUnit x :=
  isRelPrime_comm.trans isRelPrime_zero_left

@[aesop safe forward]
theorem isRelPrime_zero_right₁ : IsRelPrime x 0 → IsUnit x :=
  isRelPrime_zero_right.mp

@[aesop safe forward]
theorem isRelPrime_zero_right₂ : IsUnit x → IsRelPrime x 0 :=
  isRelPrime_zero_right.mpr

@[aesop safe apply]
theorem not_isRelPrime_zero_zero [Nontrivial α] : ¬IsRelPrime (0 : α) 0 :=
  mt isRelPrime_zero_right.mp not_isUnit_zero

@[aesop safe forward]
theorem IsRelPrime.ne_zero_or_ne_zero [Nontrivial α] (h : IsRelPrime x y) : x ≠ 0 ∨ y ≠ 0 :=
  not_or_of_imp <| by rintro rfl rfl; exact not_isRelPrime_zero_zero h

end CommMonoidWithZero

theorem isRelPrime_of_no_nonunits_factors [MonoidWithZero α] {x y : α} (nonzero : ¬(x = 0 ∧ y = 0))
    (H : ∀ z, ¬ IsUnit z → z ≠ 0 → z ∣ x → ¬z ∣ y) : IsRelPrime x y := by
  refine fun z hx hy ↦ by_contra fun h ↦ H z h ?_ hx hy
  rintro rfl; exact nonzero ⟨zero_dvd_iff.1 hx, zero_dvd_iff.1 hy⟩

theorem dvd_and_not_dvd_iff [CancelCommMonoidWithZero α] {x y : α} :
    x ∣ y ∧ ¬y ∣ x ↔ DvdNotUnit x y :=
  ⟨fun ⟨⟨d, hd⟩, hyx⟩ =>
    ⟨fun hx0 => by simp [hx0] at hyx,
      ⟨d, mt isUnit_iff_dvd_one.1 fun ⟨e, he⟩ => hyx ⟨e, by rw [hd, mul_assoc, ← he, mul_one]⟩,
        hd⟩⟩,
    fun ⟨hx0, d, hdu, hdx⟩ =>
    ⟨⟨d, hdx⟩, fun ⟨e, he⟩ =>
      hdu
        (isUnit_of_dvd_one
          ⟨e, mul_left_cancel₀ hx0 <| by conv =>
            lhs
            rw [he, hdx]
            simp [mul_assoc]⟩)⟩⟩

section MonoidWithZero

variable [MonoidWithZero α]

theorem ne_zero_of_dvd_ne_zero {p q : α} (h₁ : q ≠ 0) (h₂ : p ∣ q) : p ≠ 0 := by
  aesop

theorem isPrimal_zero : IsPrimal (0 : α) := by
  aesop (add simp [IsPrimal])

theorem IsPrimal.mul {α} [CancelCommMonoidWithZero α] {m n : α}
    (hm : IsPrimal m) (hn : IsPrimal n) : IsPrimal (m * n) := by
  obtain rfl | h0 := eq_or_ne m 0; · rwa [zero_mul]
  intro b c h
  obtain ⟨a₁, a₂, ⟨b, rfl⟩, ⟨c, rfl⟩, rfl⟩ := hm (dvd_of_mul_right_dvd h)
  rw [mul_mul_mul_comm, mul_dvd_mul_iff_left h0] at h
  obtain ⟨a₁', a₂', h₁, h₂, rfl⟩ := hn h
  exact ⟨a₁ * a₁', a₂ * a₂', mul_dvd_mul_left _ h₁, mul_dvd_mul_left _ h₂, mul_mul_mul_comm _ _ _ _⟩

end MonoidWithZero

section CancelCommMonoidWithZero

variable [CancelCommMonoidWithZero α] {a b : α} {m n : ℕ}

section Subsingleton
variable [Subsingleton αˣ]

@[aesop safe destruct]
theorem dvd_antisymm : a ∣ b → b ∣ a → a = b := by
  rintro ⟨c, rfl⟩ ⟨d, hcd⟩
  rw [mul_assoc, eq_comm, mul_right_eq_self₀, mul_eq_one] at hcd
  obtain ⟨rfl, -⟩ | rfl := hcd <;> simp

theorem dvd_antisymm' : a ∣ b → b ∣ a → b = a :=
  flip dvd_antisymm

alias Dvd.dvd.antisymm := dvd_antisymm

alias Dvd.dvd.antisymm' := dvd_antisymm'

@[aesop safe destruct]
theorem eq_of_forall_dvd (h : ∀ c, a ∣ c ↔ b ∣ c) : a = b :=
  ((h _).2 dvd_rfl).antisymm <| (h _).1 dvd_rfl

@[aesop safe destruct]
theorem eq_of_forall_dvd' (h : ∀ c, c ∣ a ↔ c ∣ b) : a = b :=
  ((h _).1 dvd_rfl).antisymm <| (h _).2 dvd_rfl

end Subsingleton

@[aesop safe forward]
lemma pow_dvd_pow_iff (ha₀ : a ≠ 0) (ha : ¬IsUnit a) : a ^ n ∣ a ^ m ↔ n ≤ m := by
  constructor
  · intro h
    rw [← not_lt]
    intro hmn
    apply ha
    have : a ^ m * a ∣ a ^ m * 1 := by
      rw [← pow_succ, mul_one]
      exact (pow_dvd_pow _ (Nat.succ_le_of_lt hmn)).trans h
    rwa [mul_dvd_mul_iff_left, ← isUnit_iff_dvd_one] at this
    apply pow_ne_zero m ha₀
  · apply pow_dvd_pow

end CancelCommMonoidWithZero
