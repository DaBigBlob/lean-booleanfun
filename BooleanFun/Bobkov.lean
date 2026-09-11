/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos
-/

import BooleanFun.Basic

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Probability.Distributions.Gaussian.Real

/-!

# Bobkov's isoperimetric inequality

## Main definitions

* Gaussian isoperimetric profile `gaussianI`

## Main theorems

* Differential equation for the Gaussian isoperimetric profile `gaussianI_mul_deriv_deriv_eq`
* Bobkov's two-point inequality `bobkov_two_point`

-/

namespace BooleanFun

noncomputable section

open Real intervalIntegral ProbabilityTheory Function Set Filter
open scoped Topology

/-- The standard Gaussian density function -/
def ϕ := gaussianPDFReal 0 1

/-- The standard Gaussian CDF.
**Note:** We prefer to avoid Mathlib's CDF implementation.
 -/
def Φ (t : ℝ) := ∫ s in Iio t, ϕ s


-- set_option pp.notation false in
/-- The range of the Gaussian CDF is the open interval `(0, 1)`. -/
-- original: theorem Φ_range : range Φ = Ioo 0 1
theorem Φ_range
  : range Φ = Ioo 0 1
  := by
  apply Set.ext
  intro x
  change (∃ i : ℝ, Φ i = x) ↔ (0 < x ∧ x < 1)
  apply Iff.intro
  .
    intro hy
    cases hy with
    | intro w h =>
      rw [← h]
      have supp_eq_univ
        : support ϕ = univ
        := by
        refine support_eq_univ ?_
        intros i ; unfold ϕ
        apply ne_of_gt -- most stuff in support seems to be <
        refine gaussianPDFReal_pos 0 1 i ?_
        norm_num
      have intg_Iio_pos
        : 0 < ∫ (s : ℝ) in Iio w, ϕ s
        := by
        refine (MeasureTheory.integral_pos_iff_support_of_nonneg ?_ ?_).mpr ?_
        .
          change ∀ r : ℝ, 0 ≤ ϕ r
          unfold ϕ
          exact fun r ↦ gaussianPDFReal_nonneg 0 1 r
        .
          apply MeasureTheory.Integrable.restrict -- ai help: (how deal with "MeasureTheory.Integrable ϕ (ℙ.restrict (Iio w))")
          unfold ϕ
          exact integrable_gaussianPDFReal 0 1
        .
          rw [supp_eq_univ]
          rw [MeasureTheory.Measure.restrict_apply_univ] -- https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/Restrict.html#MeasureTheory.Measure.restrict_apply_univ
          simp only [volume_Iio, ENNReal.zero_lt_top]
      have intg_Ici_pos
          : 0 < ∫ s in Ici w, ϕ s
          := by
          refine (MeasureTheory.integral_pos_iff_support_of_nonneg ?_ ?_).mpr ?_
          . -- copied
            change ∀ r : ℝ, 0 ≤ ϕ r
            unfold ϕ
            exact fun r ↦ gaussianPDFReal_nonneg 0 1 r
          . -- copied
            apply MeasureTheory.Integrable.restrict
            unfold ϕ
            exact integrable_gaussianPDFReal 0 1
          . -- copied
            rw [supp_eq_univ]
            rw [MeasureTheory.Measure.restrict_apply_univ]
            simp only [volume_Ici, ENNReal.zero_lt_top]
      apply And.intro
      .
        exact intg_Iio_pos
      .
        unfold Φ
        have intg_Iii_eq_1
          : ∫ s : ℝ, ϕ s = 1
          := by
          unfold ϕ
          refine integral_gaussianPDFReal_eq_one 0 ?_
          norm_num
        have intg_split
          : (∫ (s : ℝ) in Iio w, ϕ s) + (∫ (s : ℝ) in Ici w, ϕ s) = (∫ (s : ℝ), ϕ s)
          := by
          refine integral_Iio_add_Ici ?_ ?_
          .
            refine MeasureTheory.Integrable.integrableOn ?_
            exact MeasureTheory.integrable_of_integral_eq_one intg_Iii_eq_1
          .
            refine MeasureTheory.Integrable.integrableOn ?_
            exact MeasureTheory.integrable_of_integral_eq_one intg_Iii_eq_1
        rw [intg_Iii_eq_1] at intg_split
        rw [← intg_split]
        exact lt_add_of_pos_right (∫ (s : ℝ) in Iio w, ϕ s) intg_Ici_pos
  .
    intro hy
    cases hy with
    | intro ge0 le1 =>
      -- now: intermediate val
      change x ∈ range Φ
      refine mem_range_of_exists_le_of_exists_ge ?_ ?_ ?_
      .
        refine continuous_iff_continuousAt.mpr ?_
        intro t
        -- idea: contOn to contAt

        have intgϕ
          : MeasureTheory.IntegrableOn ϕ (Iio (t + 1))
          := by
          unfold ϕ
          refine MeasureTheory.Integrable.integrableOn ?_
          exact integrable_gaussianPDFReal 0 1

        have contΦ
          : ContinuousOn Φ (Iic (t + 1))
          := by
          unfold Φ
          exact MeasureTheory.IntegrableOn.continuousOn_Iic_primitive_Iio intgϕ

        apply contΦ.continuousAt
        refine Iic_mem_nhds ?_
        exact lt_add_one t
      .
        -- apply?
        sorry
      .
        sorry


set_option pp.notation false in
#print Φ
#print MeasureTheory.Integrable
#check ProbabilityTheory.gaussianPDFReal_pos
#print Function.support
#check MeasureTheory.integral_add_compl
#check integral_Iio_add_Ici

/-- The Gaussian isoperimetric profile `I = ϕ ∘ Φ⁻¹`

**Implementation note:** Mathematically, the domain of this function is `[0, 1]`, but
we extend it to the whole real line by the junk value `0`.
Careful: In Lean `Φ⁻¹` is the pointwise reciprocal, but we need the inverse function.
 -/
def gaussianI (x : ℝ) := if x ∈ Ioo 0 1 then (ϕ ∘ invFun Φ) x else 0

@[inherit_doc]
scoped notation "𝓘" => gaussianI

@[simp]
theorem gaussianI_zero
  : 𝓘 0 = 0
  := by
  simp [gaussianI]
  -- 0 is out of range (def)

@[simp]
theorem gaussianI_one
  : 𝓘 1 = 0
  := by
  simp [gaussianI]
  -- 1 is out of range (def)

-- In this section we compute derivatives of `I` on `(0, 1)`.
section gaussianI_derivatives

variable {x : ℝ}

/-- The Gaussian isoperimetric profile is differentiable on `(0, 1)` -/
theorem hasDerivAt_gaussianI (hx : x ∈ Ioo 0 1) : HasDerivAt 𝓘 (-invFun Φ x) x := by
  sorry

/-- The Gaussian isoperimetric profile's derivative.  -/
theorem deriv_gaussianI (hx : x ∈ Ioo 0 1) : deriv 𝓘 x = -invFun Φ x := by
  sorry

/-- The Gaussian isoperimetric profile is positive on `(0, 1)`. -/
-- original : theorem gaussianI_pos (hx : x ∈ Ioo 0 1) : 0 < 𝓘 x
theorem gaussianI_pos
  : {x : ℝ} -> (hx : x ∈ Ioo 0 1) -> 0 < 𝓘 x
  := by
  intro x hx ; unfold gaussianI
  rw [ite_eq_left hx]
  have l2
    : (lx : ℝ) → (0 < ϕ lx)
    := by
    intro lx ; unfold ϕ
    apply gaussianPDFReal_pos 0 1 lx
    norm_num
  change 0 < ϕ (invFun Φ x)
  exact l2 (invFun Φ x)

/-- The derivative of the Gaussian isoperimetric profile is also differentiable on `(0, 1)`. -/
theorem hasDerivAt_deriv_gaussianI (hx : x ∈ Ioo 0 1) : HasDerivAt (deriv 𝓘) (-(𝓘 x)⁻¹) x := by
  sorry

/-- The second derivative of the Gaussian isoperimetric profile -/
theorem deriv_deriv_gaussianI (hx : x ∈ Ioo 0 1) : deriv (deriv 𝓘) x = -(𝓘 x)⁻¹ := by
  sorry

/-- The second derivative of the Gaussian isoperimetric profile is negative on `(0, 1)`. -/
theorem deriv_deriv_gaussianI_neg (hx : x ∈ Ioo 0 1) : deriv (deriv 𝓘) x < 0 := by
  sorry

/-- The Gaussian isoperimetric profile is strictly concave on `[0, 1]`. -/
theorem strictConcaveOn_gaussianI : StrictConcaveOn ℝ (Icc 0 1) 𝓘 := by
  sorry

/-- Differential equation satisfied by the Gaussian isoperimetric profile. -/
theorem gaussianI_mul_deriv_deriv_eq (hx : x ∈ Ioo 0 1) :
    𝓘 x * deriv (deriv 𝓘) x = -1 := by
  sorry

/-- The limit of `I' x` tends to `∞` as `x → 0+`. -/
theorem tendsto_deriv_gaussianI_zero : Tendsto (deriv 𝓘) (𝓝[>] 0) atTop := by
  sorry

/-- The limit of `I' x` tends to `-∞` as `x → 1-`. -/
theorem tendsto_deriv_gaussianI_one : Tendsto (deriv 𝓘) (𝓝[<] 1) atBot := by
  sorry

end gaussianI_derivatives

-- In this section we prove Bobkov's two-point inequality.
section twopoint_inequality

-- Todo: formulate this correctly (for any given interval, open?)
-- /-- If a function `I` solves `I · I'' = -c` on an interval for some `0 < c`, then it is concave.
-- **Note:** In Bobkov's formulation `c = 1`.
--  -/
-- theorem concave_of_mul_deriv_deriv_eq_neg {I : ℝ → ℝ}

-- /-- If a function `I` solves `I · I'' = -c` on an interval for some `0 < c`, then `(I') ^ 2` is convex. -/
-- theorem convex_deriv_pow_two_of_mul_deriv_deriv_eq_neg

-- /-- Bobkov's classical two-point inequality for a non-negative function `I` satisfying `I · I'' = -1` on an interval. -/
-- theorem bobkov_two_point_of_mul_deriv_deriv_eq_neg

/-- Bobkov's classical two-point inequality for the Gaussian isoperimetric profile. -/
theorem bobkov_two_point {a b : ℝ} (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1) :
    2 * 𝓘 ((a + b) / 2) ≤ √((𝓘 a) ^ 2 + ((a - b) / 2) ^ 2) + √((𝓘 b) ^ 2 + ((a - b) / 2) ^ 2) := by
  sorry

end twopoint_inequality

-- ToDo: add Bobkov's isoperimetric inequality
-- The idea is that the two point inequality is the 1D case and then one can run induction on dimension

end

end BooleanFun
