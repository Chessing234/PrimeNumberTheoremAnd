import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Complex.Basic

open Complex Finset

namespace Scratch

private lemma ne_one_of_norm_lt_one {z : ℂ} (h : ‖z‖ < 1) : z ≠ 1 :=
  fun heq => by rw [heq] at h; simp at h

private lemma pow_succ_mul_eq {A x : ℂ} (k : ℕ) :
    A ^ (k + 1) * x ^ k = A * (A * x) ^ k := by
  rw [pow_succ, mul_pow]; ring

private lemma tsum_pow_succ_mul {A x : ℂ} (hAx : ‖A * x‖ < 1) :
    ∑' k : ℕ, A ^ (k + 1) * x ^ k = A * (1 - A * x)⁻¹ := by
  have hg : ∑' k : ℕ, (A * x) ^ k = (1 - A * x)⁻¹ := tsum_geometric_of_norm_lt_one hAx
  calc ∑' k : ℕ, A ^ (k + 1) * x ^ k
      = ∑' k : ℕ, A * (A * x) ^ k := tsum_congr pow_succ_mul_eq
    _ = A * ∑' k : ℕ, (A * x) ^ k := tsum_mul_left
    _ = A * (1 - A * x)⁻¹ := by rw [hg]

private lemma summable_pow_succ_mul {A x : ℂ} (hAx : ‖A * x‖ < 1) :
    Summable fun k : ℕ ↦ A ^ (k + 1) * x ^ k :=
  Summable.congr ((summable_geometric_of_norm_lt_one hAx).mul_left A)
    fun k => (pow_succ_mul_eq k).symm

private lemma tsum_four_geom
    {A B x : ℂ} (hx : ‖x‖ < 1) (hAx : ‖A * x‖ < 1) (hBx : ‖B * x‖ < 1)
    (hABx : ‖A * B * x‖ < 1) :
    (∑' k : ℕ, (A * B) ^ (k + 1) * x ^ k) -
        (∑' k : ℕ, A ^ (k + 1) * x ^ k) -
        (∑' k : ℕ, B ^ (k + 1) * x ^ k) +
        (∑' k : ℕ, x ^ k) =
      A * B * (1 - A * B * x)⁻¹ - A * (1 - A * x)⁻¹ - B * (1 - B * x)⁻¹ + (1 - x)⁻¹ := by
  rw [tsum_pow_succ_mul hABx, tsum_pow_succ_mul hAx, tsum_pow_succ_mul hBx,
    tsum_geometric_of_norm_lt_one hx]

/--
Closed form
`∑_k (∑_{i≤k} A^i)(∑_{j≤k} B^j) x^k
  = (1 - AB x²) / ((1-x)(1-Ax)(1-Bx)(1-ABx))`
when `A ≠ 1`, `B ≠ 1`, and the four geometric series converge absolutely.
-/
lemma geometric_sigma_pmul_sum
    {A B x : ℂ} (hA : A ≠ 1) (hB : B ≠ 1) (hx : ‖x‖ < 1)
    (hAx : ‖A * x‖ < 1) (hBx : ‖B * x‖ < 1) (hABx : ‖A * B * x‖ < 1) :
    ∑' k : ℕ, ((∑ i ∈ range (k + 1), A ^ i) * (∑ j ∈ range (k + 1), B ^ j) * x ^ k) =
      (1 - A * B * x ^ 2) / ((1 - x) * (1 - A * x) * (1 - B * x) * (1 - A * B * x)) := by
  have hx1 := ne_one_of_norm_lt_one hx
  have hAx1 := ne_one_of_norm_lt_one hAx
  have hBx1 := ne_one_of_norm_lt_one hBx
  have hABx1 := ne_one_of_norm_lt_one hABx
  have hsumA (k : ℕ) : ∑ i ∈ range (k + 1), A ^ i = (A ^ (k + 1) - 1) / (A - 1) :=
    geom_sum_eq hA (k + 1)
  have hsumB (k : ℕ) : ∑ j ∈ range (k + 1), B ^ j = (B ^ (k + 1) - 1) / (B - 1) :=
    geom_sum_eq hB (k + 1)
  have hs0 : Summable fun k : ℕ ↦ (x : ℂ) ^ k := summable_geometric_of_norm_lt_one hx
  have hsA := summable_pow_succ_mul (A := A) hAx
  have hsB := summable_pow_succ_mul (A := B) hBx
  have hsAB := summable_pow_succ_mul (A := A * B) hABx
  have hcongr_term (k : ℕ) :
      (A ^ (k + 1) - 1) * (B ^ (k + 1) - 1) * x ^ k =
        (A * B) ^ (k + 1) * x ^ k - A ^ (k + 1) * x ^ k - B ^ (k + 1) * x ^ k + x ^ k := by
    have hAB : (A * B) ^ (k + 1) = A ^ (k + 1) * B ^ (k + 1) := mul_pow A B (k + 1)
    rw [hAB]; ring
  have hsummable_num :
      Summable fun k : ℕ ↦ (A ^ (k + 1) - 1) * (B ^ (k + 1) - 1) * x ^ k :=
    Summable.congr (((hsAB.sub hsA).sub hsB).add hs0) fun k => (hcongr_term k).symm
  have hterm (k : ℕ) :
      (∑ i ∈ range (k + 1), A ^ i) * (∑ j ∈ range (k + 1), B ^ j) * x ^ k =
        ((A ^ (k + 1) - 1) * (B ^ (k + 1) - 1) * x ^ k) * ((A - 1) * (B - 1))⁻¹ := by
    rw [hsumA k, hsumB k]
    field_simp
  have hnum :
      ∑' k : ℕ, (A ^ (k + 1) - 1) * (B ^ (k + 1) - 1) * x ^ k =
        A * B * (1 - A * B * x)⁻¹ - A * (1 - A * x)⁻¹ - B * (1 - B * x)⁻¹ + (1 - x)⁻¹ := by
    have h1 := hsAB.sub hsA
    have h2 := h1.sub hsB
    calc ∑' k : ℕ, (A ^ (k + 1) - 1) * (B ^ (k + 1) - 1) * x ^ k
        = ∑' k : ℕ, ((A * B) ^ (k + 1) * x ^ k - A ^ (k + 1) * x ^ k -
            B ^ (k + 1) * x ^ k + x ^ k) := tsum_congr hcongr_term
      _ = (∑' k : ℕ, (A * B) ^ (k + 1) * x ^ k) - (∑' k : ℕ, A ^ (k + 1) * x ^ k) -
            (∑' k : ℕ, B ^ (k + 1) * x ^ k) + (∑' k : ℕ, x ^ k) := by
          rw [Summable.tsum_add h2 hs0, Summable.tsum_sub h1 hsB, Summable.tsum_sub hsAB hsA]
      _ = _ := tsum_four_geom hx hAx hBx hABx
  calc ∑' k : ℕ, ((∑ i ∈ range (k + 1), A ^ i) * (∑ j ∈ range (k + 1), B ^ j) * x ^ k)
      = ∑' k : ℕ, ((A ^ (k + 1) - 1) * (B ^ (k + 1) - 1) * x ^ k) * ((A - 1) * (B - 1))⁻¹ :=
        tsum_congr hterm
    _ = (∑' k : ℕ, (A ^ (k + 1) - 1) * (B ^ (k + 1) - 1) * x ^ k) * ((A - 1) * (B - 1))⁻¹ :=
        tsum_mul_right
    _ = (A * B * (1 - A * B * x)⁻¹ - A * (1 - A * x)⁻¹ - B * (1 - B * x)⁻¹ + (1 - x)⁻¹) /
          ((A - 1) * (B - 1)) := by
        rw [hnum, ← div_eq_mul_inv]
    _ = (1 - A * B * x ^ 2) / ((1 - x) * (1 - A * x) * (1 - B * x) * (1 - A * B * x)) := by
        field_simp [hx1, hAx1, hBx1, hABx1, hA, hB]
        ring

end Scratch
