/-
Copyright (c) 2023 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DedekindDomain.Ideal

/-!
# Criteria under which a Dedekind domain is a PID

This file contains some results that we can use to test whether all ideals in a Dedekind domain are
principal.

## Main results

 * `Ideal.IsPrincipal.of_finite_maximals_of_isUnit`: an invertible ideal in a commutative ring
   with finitely many maximal ideals, is a principal ideal.
 * `IsPrincipalIdealRing.of_finite_primes`: if a Dedekind domain has finitely many prime ideals,
   it is a principal ideal domain.
-/


variable {R : Type*} [CommRing R]

open Ideal

open UniqueFactorizationMonoid

open scoped nonZeroDivisors

open UniqueFactorizationMonoid

/-- Let `P` be a prime ideal, `x ∈ P \ P²` and `x ∉ Q` for all prime ideals `Q ≠ P`.
Then `P` is generated by `x`. -/
theorem Ideal.eq_span_singleton_of_mem_of_not_mem_sq_of_not_mem_prime_ne {P : Ideal R}
    (hP : P.IsPrime) [IsDedekindDomain R] {x : R} (x_mem : x ∈ P) (hxP2 : x ∉ P ^ 2)
    (hxQ : ∀ Q : Ideal R, IsPrime Q → Q ≠ P → x ∉ Q) : P = Ideal.span {x} := by
  letI := Classical.decEq (Ideal R)
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hxP2 (zero_mem _)
  by_cases hP0 : P = ⊥
  · subst hP0
    rwa [eq_comm, span_singleton_eq_bot, ← mem_bot]
  have hspan0 : span ({x} : Set R) ≠ ⊥ := mt Ideal.span_singleton_eq_bot.mp hx0
  have span_le := (Ideal.span_singleton_le_iff_mem _).mpr x_mem
  refine
    associated_iff_eq.mp
      ((associated_iff_normalizedFactors_eq_normalizedFactors hP0 hspan0).mpr
        (le_antisymm ((dvd_iff_normalizedFactors_le_normalizedFactors hP0 hspan0).mp ?_) ?_))
  · rwa [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  simp only [normalizedFactors_irreducible (Ideal.prime_of_isPrime hP0 hP).irreducible,
    normalize_eq, Multiset.le_iff_count, Multiset.count_singleton]
  intro Q
  split_ifs with hQ
  · subst hQ
    refine (Ideal.count_normalizedFactors_eq ?_ ?_).le <;>
        simp only [Ideal.span_singleton_le_iff_mem, pow_one] <;>
      assumption
  by_cases hQp : IsPrime Q
  · refine (Ideal.count_normalizedFactors_eq ?_ ?_).le <;>
      -- Porting note: included `zero_add` in the simp arguments
      simp only [Ideal.span_singleton_le_iff_mem, zero_add, pow_one, pow_zero, one_eq_top,
                 Submodule.mem_top]
    exact hxQ _ hQp hQ
  · exact
      (Multiset.count_eq_zero.mpr fun hQi =>
          hQp
            (isPrime_of_prime
              (irreducible_iff_prime.mp (irreducible_of_normalized_factor _ hQi)))).le

-- Porting note: replaced three implicit coercions of `I` with explicit `(I : Submodule R A)`
theorem FractionalIdeal.isPrincipal_of_unit_of_comap_mul_span_singleton_eq_top {R A : Type*}
    [CommRing R] [CommRing A] [Algebra R A] {S : Submonoid R} [IsLocalization S A]
    (I : (FractionalIdeal S A)ˣ) {v : A} (hv : v ∈ (↑I⁻¹ : FractionalIdeal S A))
    (h : Submodule.comap (Algebra.linearMap R A) ((I : Submodule R A) * Submodule.span R {v}) = ⊤) :
    Submodule.IsPrincipal (I : Submodule R A) := by
  have hinv := I.mul_inv
  set J := Submodule.comap (Algebra.linearMap R A) ((I : Submodule R A) * Submodule.span R {v})
  have hJ : IsLocalization.coeSubmodule A J = ↑I * Submodule.span R {v} := by
    -- Porting note: had to insert `val_eq_coe` into this rewrite.
    -- Arguably this is because `Subtype.ext_iff` is breaking the `FractionalIdeal` API.
    rw [Subtype.ext_iff, val_eq_coe, coe_mul, val_eq_coe, coe_one] at hinv
    apply Submodule.map_comap_eq_self
    rw [← Submodule.one_eq_range, ← hinv]
    exact Submodule.mul_le_mul_right ((Submodule.span_singleton_le_iff_mem _ _).2 hv)
  have : (1 : A) ∈ ↑I * Submodule.span R {v} := by
    rw [← hJ, h, IsLocalization.coeSubmodule_top, Submodule.mem_one]
    exact ⟨1, (algebraMap R _).map_one⟩
  obtain ⟨w, hw, hvw⟩ := Submodule.mem_mul_span_singleton.1 this
  refine ⟨⟨w, ?_⟩⟩
  rw [← FractionalIdeal.coe_spanSingleton S, ← inv_inv I, eq_comm]
  refine congr_arg coeToSubmodule (Units.eq_inv_of_mul_eq_one_left (le_antisymm ?_ ?_))
  · conv_rhs => rw [← hinv, mul_comm]
    apply FractionalIdeal.mul_le_mul_left (FractionalIdeal.spanSingleton_le_iff_mem.mpr hw)
  · rw [FractionalIdeal.one_le, ← hvw, mul_comm]
    exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _) hv

/--
An invertible fractional ideal of a commutative ring with finitely many maximal ideals is principal.

https://math.stackexchange.com/a/95857 -/
theorem FractionalIdeal.isPrincipal.of_finite_maximals_of_inv {A : Type*} [CommRing A]
    [Algebra R A] {S : Submonoid R} [IsLocalization S A] (hS : S ≤ R⁰)
    (hf : {I : Ideal R | I.IsMaximal}.Finite) (I I' : FractionalIdeal S A) (hinv : I * I' = 1) :
    Submodule.IsPrincipal (I : Submodule R A) := by
  have hinv' := hinv
  rw [Subtype.ext_iff, val_eq_coe, coe_mul] at hinv
  let s := hf.toFinset
  haveI := Classical.decEq (Ideal R)
  have coprime : ∀ M ∈ s, ∀ M' ∈ s.erase M, M ⊔ M' = ⊤ := by
    simp_rw [s, Finset.mem_erase, hf.mem_toFinset]
    rintro M hM M' ⟨hne, hM'⟩
    exact Ideal.IsMaximal.coprime_of_ne hM hM' hne.symm
  have nle : ∀ M ∈ s, ¬⨅ M' ∈ s.erase M, M' ≤ M := fun M hM =>
    left_lt_sup.1
      ((hf.mem_toFinset.1 hM).ne_top.lt_top.trans_eq (Ideal.sup_iInf_eq_top <| coprime M hM).symm)
  have : ∀ M ∈ s, ∃ a ∈ I, ∃ b ∈ I', a * b ∉ IsLocalization.coeSubmodule A M := by
    intro M hM; by_contra! h
    obtain ⟨x, hx, hxM⟩ :=
      SetLike.exists_of_lt
        ((IsLocalization.coeSubmodule_strictMono hS (hf.mem_toFinset.1 hM).ne_top.lt_top).trans_eq
          hinv.symm)
    exact hxM (Submodule.mul_le.2 h hx)
  choose! a ha b hb hm using this
  choose! u hu hum using fun M hM => SetLike.not_le_iff_exists.1 (nle M hM)
  let v := ∑ M ∈ s, u M • b M
  have hv : v ∈ I' := Submodule.sum_mem _ fun M hM => Submodule.smul_mem _ _ <| hb M hM
  refine
    FractionalIdeal.isPrincipal_of_unit_of_comap_mul_span_singleton_eq_top
      (Units.mkOfMulEqOne I I' hinv') hv (of_not_not fun h => ?_)
  obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal _ h
  replace hM := hf.mem_toFinset.2 hM
  have : ∀ a ∈ I, ∀ b ∈ I', ∃ c, algebraMap R _ c = a * b := by
    intro a ha b hb; have hi := hinv.le
    obtain ⟨c, -, hc⟩ := hi (Submodule.mul_mem_mul ha hb)
    exact ⟨c, hc⟩
  have hmem : a M * v ∈ IsLocalization.coeSubmodule A M := by
    obtain ⟨c, hc⟩ := this _ (ha M hM) v hv
    refine IsLocalization.coeSubmodule_mono _ hJM ⟨c, ?_, hc⟩
    have := Submodule.mul_mem_mul (ha M hM) (Submodule.mem_span_singleton_self v)
    rwa [← hc] at this
  simp_rw [v, Finset.mul_sum, mul_smul_comm] at hmem
  rw [← s.add_sum_erase _ hM, Submodule.add_mem_iff_left] at hmem
  · refine hm M hM ?_
    obtain ⟨c, hc : algebraMap R A c = a M * b M⟩ := this _ (ha M hM) _ (hb M hM)
    rw [← hc] at hmem ⊢
    rw [Algebra.smul_def, ← _root_.map_mul] at hmem
    obtain ⟨d, hdM, he⟩ := hmem
    rw [IsLocalization.injective _ hS he] at hdM
    -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to specify the value of `f`
    exact Submodule.mem_map_of_mem (f := Algebra.linearMap _ _)
        (((hf.mem_toFinset.1 hM).isPrime.mem_or_mem hdM).resolve_left <| hum M hM)
  · refine Submodule.sum_mem _ fun M' hM' => ?_
    rw [Finset.mem_erase] at hM'
    obtain ⟨c, hc⟩ := this _ (ha M hM) _ (hb M' hM'.2)
    rw [← hc, Algebra.smul_def, ← _root_.map_mul]
    specialize hu M' hM'.2
    simp_rw [Ideal.mem_iInf, Finset.mem_erase] at hu
    -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to specify the value of `f`
    exact Submodule.mem_map_of_mem (f := Algebra.linearMap _ _)
      (M.mul_mem_right _ <| hu M ⟨hM'.1.symm, hM⟩)

/-- An invertible ideal in a commutative ring with finitely many maximal ideals is principal.

https://math.stackexchange.com/a/95857 -/
theorem Ideal.IsPrincipal.of_finite_maximals_of_isUnit (hf : {I : Ideal R | I.IsMaximal}.Finite)
    {I : Ideal R} (hI : IsUnit (I : FractionalIdeal R⁰ (FractionRing R))) : I.IsPrincipal :=
  (IsLocalization.coeSubmodule_isPrincipal _ le_rfl).mp
    (FractionalIdeal.isPrincipal.of_finite_maximals_of_inv le_rfl hf I
      (↑hI.unit⁻¹ : FractionalIdeal R⁰ (FractionRing R)) hI.unit.mul_inv)

/-- A Dedekind domain is a PID if its set of primes is finite. -/
theorem IsPrincipalIdealRing.of_finite_primes [IsDedekindDomain R]
    (h : {I : Ideal R | I.IsPrime}.Finite) : IsPrincipalIdealRing R :=
  ⟨fun I => by
    obtain rfl | hI := eq_or_ne I ⊥
    · exact bot_isPrincipal
    apply Ideal.IsPrincipal.of_finite_maximals_of_isUnit
    · apply h.subset; exact @Ideal.IsMaximal.isPrime _ _
    · exact isUnit_of_mul_eq_one _ _ (FractionalIdeal.coe_ideal_mul_inv I hI)⟩

variable [IsDedekindDomain R]
variable (S : Type*) [CommRing S]
variable [Algebra R S] [Module.Free R S] [Module.Finite R S]
variable (p : Ideal R) (hp0 : p ≠ ⊥) [IsPrime p]
variable {Sₚ : Type*} [CommRing Sₚ] [Algebra S Sₚ]
variable [IsLocalization (Algebra.algebraMapSubmonoid S p.primeCompl) Sₚ]
variable [Algebra R Sₚ] [IsScalarTower R S Sₚ]
include hp0

/- The first hypothesis below follows from properties of the localization but is needed for the
second, so we leave it to the user to provide (automatically). -/
variable [IsDedekindDomain Sₚ]

/-- If `p` is a prime in the Dedekind domain `R`, `S` an extension of `R` and `Sₚ` the localization
of `S` at `p`, then all primes in `Sₚ` are factors of the image of `p` in `Sₚ`. -/
theorem IsLocalization.OverPrime.mem_normalizedFactors_of_isPrime [IsDomain S]
    {P : Ideal Sₚ} (hP : IsPrime P) (hP0 : P ≠ ⊥) :
    P ∈ normalizedFactors (Ideal.map (algebraMap R Sₚ) p) := by
  have non_zero_div : Algebra.algebraMapSubmonoid S p.primeCompl ≤ S⁰ :=
    map_le_nonZeroDivisors_of_injective _ (NoZeroSMulDivisors.algebraMap_injective _ _)
      p.primeCompl_le_nonZeroDivisors
  letI : Algebra (Localization.AtPrime p) Sₚ := localizationAlgebra p.primeCompl S
  haveI : IsScalarTower R (Localization.AtPrime p) Sₚ :=
    IsScalarTower.of_algebraMap_eq fun x => by
      -- Porting note: replaced `erw` with a `rw` followed by `exact` to help infer implicits
      rw [IsScalarTower.algebraMap_apply R S]
      exact (IsLocalization.map_eq (T := Algebra.algebraMapSubmonoid S (primeCompl p))
        (Submonoid.le_comap_map _) x).symm
  obtain ⟨pid, p', ⟨hp'0, hp'p⟩, hpu⟩ :=
    (DiscreteValuationRing.iff_pid_with_one_nonzero_prime (Localization.AtPrime p)).mp
      (IsLocalization.AtPrime.discreteValuationRing_of_dedekind_domain R hp0 _)
  have : IsLocalRing.maximalIdeal (Localization.AtPrime p) ≠ ⊥ := by
    rw [Submodule.ne_bot_iff] at hp0 ⊢
    obtain ⟨x, x_mem, x_ne⟩ := hp0
    exact
      ⟨algebraMap _ _ x, (IsLocalization.AtPrime.to_map_mem_maximal_iff _ _ _).mpr x_mem,
        IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors _ p.primeCompl_le_nonZeroDivisors
          (mem_nonZeroDivisors_of_ne_zero x_ne)⟩
  rw [← Multiset.singleton_le, ← normalize_eq P, ←
    normalizedFactors_irreducible (Ideal.prime_of_isPrime hP0 hP).irreducible, ←
    dvd_iff_normalizedFactors_le_normalizedFactors hP0, dvd_iff_le,
    IsScalarTower.algebraMap_eq R (Localization.AtPrime p) Sₚ, ← Ideal.map_map,
    Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap,
    hpu (IsLocalRing.maximalIdeal _) ⟨this, _⟩, hpu (comap _ _) ⟨_, _⟩]
  · have : Algebra.IsIntegral (Localization.AtPrime p) Sₚ := ⟨isIntegral_localization⟩
    exact mt (Ideal.eq_bot_of_comap_eq_bot ) hP0
  · exact Ideal.comap_isPrime (algebraMap (Localization.AtPrime p) Sₚ) P
  · exact (IsLocalRing.maximalIdeal.isMaximal _).isPrime
  · rw [Ne, zero_eq_bot, Ideal.map_eq_bot_iff_of_injective]
    · assumption
    rw [IsScalarTower.algebraMap_eq R S Sₚ]
    exact
      (IsLocalization.injective Sₚ non_zero_div).comp (NoZeroSMulDivisors.algebraMap_injective _ _)

/-- Let `p` be a prime in the Dedekind domain `R` and `S` be an integral extension of `R`,
then the localization `Sₚ` of `S` at `p` is a PID. -/
theorem IsDedekindDomain.isPrincipalIdealRing_localization_over_prime [IsDomain S] :
    IsPrincipalIdealRing Sₚ := by
  letI := Classical.decEq (Ideal Sₚ)
  letI := Classical.decPred fun P : Ideal Sₚ => P.IsPrime
  refine
    IsPrincipalIdealRing.of_finite_primes
      (Set.Finite.ofFinset
        (Finset.filter (fun P => P.IsPrime)
          ({⊥} ∪ (normalizedFactors (Ideal.map (algebraMap R Sₚ) p)).toFinset))
        fun P => ?_)
  rw [Finset.mem_filter, Finset.mem_union, Finset.mem_singleton, Set.mem_setOf,
    Multiset.mem_toFinset]
  exact
    and_iff_right_of_imp fun hP =>
      or_iff_not_imp_left.mpr (IsLocalization.OverPrime.mem_normalizedFactors_of_isPrime S p hp0 hP)