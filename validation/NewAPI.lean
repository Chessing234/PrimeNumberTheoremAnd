import PrimeNumberTheoremAnd.IwaniecKowalskiCh1
import PrimeNumberTheoremAnd.Auxiliary
import PrimeNumberTheoremAnd.Mathlib.Algebra.Notation.Support
import PrimeNumberTheoremAnd.Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Measurability

open ArithmeticFunction MeasureTheory Filter Topology

-- The support API now works with zero divisors, vector values, and discrete domains.
example {f g : ℕ → ZMod 6} {s : Set ℕ} (hf : f.support ⊆ s) :
    (f * g).support ⊆ s := Function.support_mul_subset_of_subset hf

example (f : ℕ → ℝ × ℝ) : (fun n ↦ ‖f n‖).support = f.support :=
  Function.support_abs f

example {f : ℕ → ℝ} : (fun n ↦ (f n : ℂ)).support = f.support :=
  Function.support_ofReal

-- Constant-limit uniqueness can now use a natural-number source filter and real target.
example (a b : ℝ) (f : ℕ → ℝ) (hf : ∀ᶠ n in atTop, f n = 0)
    (hlim : Tendsto f atTop (𝓝 (b - a))) : a = b := zeroTendstoDiff a b f hf hlim

-- Integral localization can now use a discrete source space.
example {f : ℕ → ℝ} {s t : Set ℕ} (hf : f.support ⊆ t) :
    ∫ n in s, f n ∂Measure.count = ∫ n in s ∩ t, f n ∂Measure.count :=
  SetIntegral.integral_eq_integral_inter_of_support_subset hf (by measurability)

#print axioms IsAdditive.map_one
#print axioms IsCompletelyAdditive.map_one
#print axioms IsCompletelyAdditive.map_pow
#print axioms IsAdditive.add
#print axioms IsCompletelyAdditive.add
#print axioms LSeriesSummable.of_coeff_norm_le
#print axioms LSeries.term_isMultiplicative
#print axioms LSeriesSummable.on_prime_powers
#print axioms LSeriesSummable.sumOnPrimePows_eq
#print axioms zeroTendstoDiff
#print axioms limitOfConstant
#print axioms limitOfConstantLeft
#print axioms Function.support_abs
#print axioms Function.support_ofReal
#print axioms Function.support_mul_subset_of_subset
#print axioms Function.support_of_along_fiber_subset_subset
#print axioms MeasureTheory.setIntegral_integral_swap
#print axioms SetIntegral.integral_eq_integral_inter_of_support_subset
#print axioms SetIntegral.integral_eq_integral_inter_of_support_subset_Icc
