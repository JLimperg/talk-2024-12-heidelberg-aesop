/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Yaël Dillies
-/

import Mathlib.GroupTheory.Perm.Cycle.Basic

/-!
# Closure results for permutation groups

* This file contains several closure results:
* `closure_isCycle` : The symmetric group is generated by cycles
* `closure_cycle_adjacent_swap` : The symmetric group is generated by
    a cycle and an adjacent transposition
* `closure_cycle_coprime_swap` : The symmetric group is generated by
    a cycle and a coprime transposition
* `closure_prime_cycle_swap` : The symmetric group is generated by
    a prime cycle and a transposition

-/

open Equiv Function Finset

variable {ι α β : Type*}

namespace Equiv.Perm

section Generation

variable [Finite β]

open Subgroup

theorem closure_isCycle : closure { σ : Perm β | IsCycle σ } = ⊤ := by
  classical
    cases nonempty_fintype β
    exact
      top_le_iff.mp (le_trans (ge_of_eq closure_isSwap) (closure_mono fun _ => IsSwap.isCycle))

variable [DecidableEq α] [Fintype α]

theorem closure_cycle_adjacent_swap {σ : Perm α} (h1 : IsCycle σ) (h2 : σ.support = univ) (x : α) :
    closure ({σ, swap x (σ x)} : Set (Perm α)) = ⊤ := by
  let H := closure ({σ, swap x (σ x)} : Set (Perm α))
  have h3 : σ ∈ H := subset_closure (Set.mem_insert σ _)
  have h4 : swap x (σ x) ∈ H := subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have step1 : ∀ n : ℕ, swap ((σ ^ n) x) ((σ ^ (n + 1) : Perm α) x) ∈ H := by
    intro n
    induction n with
    | zero => exact subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    | succ n ih =>
      convert H.mul_mem (H.mul_mem h3 ih) (H.inv_mem h3)
      simp_rw [mul_swap_eq_swap_mul, mul_inv_cancel_right, pow_succ', coe_mul, comp_apply]
  have step2 : ∀ n : ℕ, swap x ((σ ^ n) x) ∈ H := by
    intro n
    induction n with
    | zero =>
      simp only [pow_zero, coe_one, id_eq, swap_self, Set.mem_singleton_iff]
      convert H.one_mem
    | succ n ih =>
      by_cases h5 : x = (σ ^ n) x
      · rw [pow_succ', mul_apply, ← h5]
        exact h4
      by_cases h6 : x = (σ ^ (n + 1) : Perm α) x
      · rw [← h6, swap_self]
        exact H.one_mem
      rw [swap_comm, ← swap_mul_swap_mul_swap h5 h6]
      exact H.mul_mem (H.mul_mem (step1 n) ih) (step1 n)
  have step3 : ∀ y : α, swap x y ∈ H := by
    intro y
    have hx : x ∈ univ := Finset.mem_univ x
    rw [← h2, mem_support] at hx
    have hy : y ∈ univ := Finset.mem_univ y
    rw [← h2, mem_support] at hy
    cases' IsCycle.exists_pow_eq h1 hx hy with n hn
    rw [← hn]
    exact step2 n
  have step4 : ∀ y z : α, swap y z ∈ H := by
    intro y z
    by_cases h5 : z = x
    · rw [h5, swap_comm]
      exact step3 y
    by_cases h6 : z = y
    · rw [h6, swap_self]
      exact H.one_mem
    rw [← swap_mul_swap_mul_swap h5 h6, swap_comm z x]
    exact H.mul_mem (H.mul_mem (step3 y) (step3 z)) (step3 y)
  rw [eq_top_iff, ← closure_isSwap, closure_le]
  rintro τ ⟨y, z, _, h6⟩
  rw [h6]
  exact step4 y z

theorem closure_cycle_coprime_swap {n : ℕ} {σ : Perm α} (h0 : Nat.Coprime n (Fintype.card α))
    (h1 : IsCycle σ) (h2 : σ.support = Finset.univ) (x : α) :
    closure ({σ, swap x ((σ ^ n) x)} : Set (Perm α)) = ⊤ := by
  rw [← Finset.card_univ, ← h2, ← h1.orderOf] at h0
  cases' exists_pow_eq_self_of_coprime h0 with m hm
  have h2' : (σ ^ n).support = univ := Eq.trans (support_pow_coprime h0) h2
  have h1' : IsCycle ((σ ^ n) ^ (m : ℤ)) := by rwa [← hm] at h1
  replace h1' : IsCycle (σ ^ n) :=
    h1'.of_pow (le_trans (support_pow_le σ n) (ge_of_eq (congr_arg support hm)))
  rw [eq_top_iff, ← closure_cycle_adjacent_swap h1' h2' x, closure_le, Set.insert_subset_iff]
  exact
    ⟨Subgroup.pow_mem (closure _) (subset_closure (Set.mem_insert σ _)) n,
      Set.singleton_subset_iff.mpr (subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))⟩

theorem closure_prime_cycle_swap {σ τ : Perm α} (h0 : (Fintype.card α).Prime) (h1 : IsCycle σ)
    (h2 : σ.support = Finset.univ) (h3 : IsSwap τ) : closure ({σ, τ} : Set (Perm α)) = ⊤ := by
  obtain ⟨x, y, h4, h5⟩ := h3
  obtain ⟨i, hi⟩ :=
    h1.exists_pow_eq (mem_support.mp ((Finset.ext_iff.mp h2 x).mpr (Finset.mem_univ x)))
      (mem_support.mp ((Finset.ext_iff.mp h2 y).mpr (Finset.mem_univ y)))
  rw [h5, ← hi]
  refine closure_cycle_coprime_swap
    (Nat.Coprime.symm (h0.coprime_iff_not_dvd.mpr fun h => h4 ?_)) h1 h2 x
  cases' h with m hm
  rwa [hm, pow_mul, ← Finset.card_univ, ← h2, ← h1.orderOf, pow_orderOf_eq_one, one_pow,
    one_apply] at hi

end Generation

end Perm

end Equiv