-- Author: Jonathan f(n) Reed
-- Licensed under the MIT License.

import Mathlib

noncomputable section

open Polynomial

-- ====================================================================
-- Step 1: Base Ring and Polynomial Definitions
-- ====================================================================

def phi_nine : Polynomial ℤ := X^6 + X^3 + 1
def target_cubic : Polynomial ℤ := X^3 - 3*X + 1
def shifted_cubic : Polynomial ℤ := X^3 - 3*X^2 + 3

-- ====================================================================
-- Step 2: Variable Substitution and Irreducibility
-- ====================================================================

lemma shifted_cubic_comp_eq : shifted_cubic = target_cubic.comp (X - 1) := by
  unfold shifted_cubic target_cubic Polynomial.comp
  simp [eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_X]
  ring

lemma shifted_cubic_irreducible : Irreducible shifted_cubic := by
  let P : Ideal ℤ := Ideal.span {(3 : ℤ)}
  
  have hP : P.IsPrime := by
    rw [Ideal.span_singleton_prime (by norm_num)]
    exact Int.prime_three

  have h_deg_nat : shifted_cubic.natDegree = 3 := by
    unfold shifted_cubic
    compute_degree!

  have h_deg_ne : shifted_cubic ≠ 0 := by 
    intro h
    rw [h] at h_deg_nat
    norm_num at h_deg_nat

  have h_lead : shifted_cubic.leadingCoeff = 1 := by
    unfold shifted_cubic
    rw [leadingCoeff]
    have h_nat : (X^3 - 3 * X^2 + 3 : Polynomial ℤ).natDegree = 3 := by compute_degree!
    rw [h_nat]
    norm_num

  have h_prim : shifted_cubic.IsPrimitive := by
    have h_monic : shifted_cubic.Monic := by
      rw [Monic, h_lead]
    exact h_monic.isPrimitive

  apply Polynomial.irreducible_of_eisenstein_criterion hP
  · intro h_mem
    rcases Ideal.mem_span_singleton.mp h_mem with ⟨c, hc⟩
    rw [h_lead] at hc
    omega
  · intro n hn
    have h_deg_val : shifted_cubic.degree = 3 := by 
      rw [degree_eq_natDegree h_deg_ne, h_deg_nat]
      rfl
    have h_lt : n < 3 := by
      rw [h_deg_val] at hn
      have hn' : (n : WithBot ℕ) < (3 : WithBot ℕ) := hn
      exact_mod_cast hn'
    rcases n with _ | _ | _ | n
    · have h_c0 : shifted_cubic.coeff 0 = 3 := by 
        unfold shifted_cubic
        simp
      rw [h_c0]
      exact Ideal.subset_span (Set.mem_singleton 3)
    · have h_c1 : shifted_cubic.coeff 1 = 0 := by 
        unfold shifted_cubic
        simp
      rw [h_c1]
      exact Submodule.zero_mem _
    · have h_c2 : shifted_cubic.coeff 2 = -3 := by 
        unfold shifted_cubic
        simp
      rw [h_c2]
      rw [← Ideal.neg_mem_iff]
      exact Ideal.subset_span (Set.mem_singleton 3)
    · omega
  · rw [degree_eq_natDegree h_deg_ne, h_deg_nat]
    exact WithBot.coe_lt_coe.mpr (by norm_num)
  · intro h_mem
    have h_const : shifted_cubic.coeff 0 = 3 := by 
      unfold shifted_cubic
      simp
    rw [h_const] at h_mem
    have h_P2 : P ^ 2 = Ideal.span {(9 : ℤ)} := by
      unfold P
      rw [Ideal.span_singleton_pow]
      norm_num
    rw [h_P2] at h_mem
    rcases Ideal.mem_span_singleton.mp h_mem with ⟨d, hd⟩
    omega
  · exact h_prim

-- ====================================================================
-- Step 3: Gauss's Lemma and Rational Lifting
-- ====================================================================

lemma target_cubic_monic : Monic target_cubic := by
  unfold target_cubic
  rw [Monic, leadingCoeff]
  have h_deg : (X^3 - 3 * X + 1 : Polynomial ℤ).natDegree = 3 := by compute_degree!
  rw [h_deg]
  change (X^3).coeff 3 - (3 * X).coeff 3 + (1 : Polynomial ℤ).coeff 3 = 1
  rw [coeff_X_pow, if_pos rfl]
  have h3x : (3 * X : Polynomial ℤ).coeff 3 = 0 := by
    have h_c : (3 * X : Polynomial ℤ) = C 3 * X := rfl
    rw [h_c, coeff_C_mul, coeff_X]
    rw [if_neg (by norm_num)]
    ring
  have h1 : (1 : Polynomial ℤ).coeff 3 = 0 := by
    have h_c1 : (1 : Polynomial ℤ) = C 1 := rfl
    rw [h_c1, coeff_C]
    rw [if_neg (by norm_num)]
  rw [h3x, h1]
  norm_num

lemma target_cubic_irreducible_int : Irreducible target_cubic := by
  constructor
  · intro h_unit
    have h_deg : target_cubic.natDegree = 3 := by unfold target_cubic; compute_degree!
    have h_zero : target_cubic.natDegree = 0 := natDegree_eq_zero_of_isUnit h_unit
    omega
  · intro a b hab
    have h_shift : shifted_cubic = (a.comp (X - 1)) * (b.comp (X - 1)) := by
      rw [shifted_cubic_comp_eq, hab]
      ext i
      simp [Polynomial.comp]
    rcases @Irreducible.isUnit_or_isUnit _ _ _ shifted_cubic_irreducible (a.comp (X - 1)) (b.comp (X - 1)) h_shift with h_ua | h_ub
    · left
      have h_inv : (a.comp (X - 1)).comp (X + 1) = a := by
        rw [Polynomial.comp_assoc]
        have h_inner : (X - (1 : Polynomial ℤ)).comp (X + 1) = X := by
          ext i
          simp [Polynomial.comp]
        rw [h_inner, Polynomial.comp_X]
      have h_map := h_ua.map (Polynomial.eval₂RingHom Polynomial.C (X + 1 : Polynomial ℤ))
      have h_eq : (eval₂RingHom Polynomial.C (X + 1 : Polynomial ℤ)) (a.comp (X - 1)) = a := by
        ext i
        simp [eval₂_comp]
      exact h_eq ▸ h_map
    · right
      have h_inv : (b.comp (X - 1)).comp (X + 1) = b := by
        rw [Polynomial.comp_assoc]
        have h_inner : (X - (1 : Polynomial ℤ)).comp (X + 1) = X := by
          ext i
          simp [Polynomial.comp]
        rw [h_inner, Polynomial.comp_X]
      have h_map := h_ub.map (Polynomial.eval₂RingHom Polynomial.C (X + 1 : Polynomial ℤ))
      have h_eq : (eval₂RingHom Polynomial.C (X + 1 : Polynomial ℤ)) (b.comp (X - 1)) = b := by
        ext i
        simp [eval₂_comp]
      exact h_eq ▸ h_map

-- ====================================================================
-- Step 4: Inductive Identity Generation (Chord Sequence / Chebyshev)
-- ====================================================================

def chebyshev_rel : ℕ → Polynomial ℤ
  | 0 => 3
  | 1 => X
  | n + 2 => C 2 * X * chebyshev_rel (n + 1) - chebyshev_rel n

lemma chebyshev_recurrence (n : ℕ) : 
    chebyshev_rel (n + 2) = C 2 * X * chebyshev_rel (n + 1) - chebyshev_rel n := by
  rfl

lemma chebyshev_natDegree_le (k : ℕ) : 
    (chebyshev_rel k).natDegree ≤ k := by
  induction' k using Nat.strong_induction_on with k ih
  rcases k with _ | _ | n
  · unfold chebyshev_rel; norm_num
  · unfold chebyshev_rel; norm_num
  · rw [chebyshev_recurrence]
    have h_sub : (C 2 * X * chebyshev_rel (n + 1) - chebyshev_rel n).natDegree ≤ 
        max (C 2 * X * chebyshev_rel (n + 1)).natDegree (chebyshev_rel n).natDegree := 
      natDegree_sub_le _ _
    have h_ih_n : (chebyshev_rel n).natDegree ≤ n + 2 := le_trans (ih n (by omega)) (by omega)
    refine le_trans h_sub (max_le ?_ h_ih_n)
    calc (C 2 * X * chebyshev_rel (n + 1)).natDegree 
      _ ≤ (C 2 * X : Polynomial ℤ).natDegree + (chebyshev_rel (n + 1)).natDegree := natDegree_mul_le
      _ ≤ 1 + (n + 1) := by 
          apply add_le_add 
          · have h_cx : (C 2 * X : Polynomial ℤ) = C 2 * X := rfl
            rw [h_cx]
            have h_c2_ne : (C 2 : Polynomial ℤ) ≠ 0 := by intro h; have := congr_arg (coeff · 0) h; norm_num at this
            have h_x_ne : (X : Polynomial ℤ) ≠ 0 := X_ne_zero
            rw [natDegree_mul h_c2_ne h_x_ne, natDegree_C, zero_add, natDegree_X]
          · exact ih (n + 1) (by omega)
      _ = n + 2 := by omega

-- ====================================================================
-- Step 5: Homomorphic Evaluation and Ideal Membership
-- ====================================================================

lemma closed_form_evaluation (zeta : ℂ) (h_root : eval₂ (Int.castRingHom ℂ) zeta phi_nine = 0) : 
    eval₂ (Int.castRingHom ℂ) (zeta + zeta⁻¹) target_cubic = 0 := by
  have h_zeta_poly : zeta^6 + zeta^3 + 1 = 0 := by
    have h_eval_phi := h_root
    unfold phi_nine at h_eval_phi
    simp [eval₂_add, eval₂_pow, eval₂_one, eval₂_X] at h_eval_phi
    exact h_eval_phi
  have h_nonzero : zeta ≠ 0 := by
    intro h_z
    have h_sub := h_zeta_poly
    rw [h_z] at h_sub
    norm_num at h_sub
  have h_z3 : zeta^3 ≠ 0 := pow_ne_zero 3 h_nonzero
  unfold target_cubic
  simp [eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_X, eval₂_one]
  have h_id : (zeta + zeta⁻¹)^3 - 3 * (zeta + zeta⁻¹) + 1 = (zeta^6 + zeta^3 + 1) / zeta^3 := by
    field_simp [h_z3]
    ring
  rw [h_id, h_zeta_poly, zero_div]