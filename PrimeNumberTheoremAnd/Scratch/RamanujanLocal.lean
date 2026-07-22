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

/-- ∑ (k+1)² xᵏ = (1+x)/(1-x)³ = (1-x²)/(1-x)⁴ for ‖x‖ < 1. -/
lemma tsum_succ_sq_mul_geometric {x : ℂ} (hx : ‖x‖ < 1) :
    ∑' k : ℕ, ((k + 1 : ℂ) ^ 2) * x ^ k = (1 + x) / (1 - x) ^ 3 := by
  have h2 := tsum_choose_mul_geometric_of_norm_lt_one (k := 2) (𝕜 := ℂ) hx
  have h1 := tsum_choose_mul_geometric_of_norm_lt_one (k := 1) (𝕜 := ℂ) hx
  have hsA : Summable fun k : ℕ ↦ (2 : ℂ) * (↑((k + 2).choose 2) * x ^ k) :=
    (summable_choose_mul_geometric_of_norm_lt_one (R := ℂ) 2 hx).mul_left (2 : ℂ)
  have hsB : Summable fun k : ℕ ↦ ↑((k + 1).choose 1) * x ^ k :=
    summable_choose_mul_geometric_of_norm_lt_one (R := ℂ) 1 hx
  have hid (k : ℕ) :
      ((k + 1 : ℂ) ^ 2) = 2 * ↑((k + 2).choose 2) - ↑(k + 1) := by
    have hn : 2 * (k + 2).choose 2 = (k + 2) * (k + 1) := by
      rw [Nat.choose_two_right]
      exact Nat.mul_div_cancel' (by
        simpa [mul_comm, ← even_iff_two_dvd] using Nat.even_mul_succ_self (k + 1))
    have hC : (2 : ℂ) * ↑((k + 2).choose 2) = (↑k + 2) * (↑k + 1) := by
      exact_mod_cast hn
    rw [hC]; push_cast; ring
  have hcongr (k : ℕ) :
      ((k + 1 : ℂ) ^ 2) * x ^ k =
        (2 : ℂ) * (↑((k + 2).choose 2) * x ^ k) - ↑((k + 1).choose 1) * x ^ k := by
    rw [hid k, Nat.choose_one_right, sub_mul]; ring
  rw [tsum_congr hcongr, Summable.tsum_sub hsA hsB, tsum_mul_left, h2, h1]
  have hx1 : x ≠ 1 := ne_one_of_norm_lt_one hx
  field_simp [hx1]
  ring

/-- When A = B = 1, the Ramanujan local factor is (1-x²)/(1-x)⁴. -/
lemma geometric_sigma_pmul_sum_one_one {x : ℂ} (hx : ‖x‖ < 1) :
    ∑' k : ℕ, ((∑ i ∈ range (k + 1), (1 : ℂ) ^ i) * (∑ j ∈ range (k + 1), (1 : ℂ) ^ j) * x ^ k) =
      (1 - x ^ 2) / (1 - x) ^ 4 := by
  have honesum (k : ℕ) : ∑ i ∈ range (k + 1), (1 : ℂ) ^ i = ↑(k + 1) := by
    simp [sum_const, card_range, nsmul_eq_mul]
  have hsimp (k : ℕ) :
      (∑ i ∈ range (k + 1), (1 : ℂ) ^ i) * (∑ j ∈ range (k + 1), (1 : ℂ) ^ j) * x ^ k =
        ((k + 1 : ℂ) ^ 2) * x ^ k := by
    have sA := honesum k
    nth_rw 1 [sA]
    nth_rw 1 [sA]
    push_cast
    ring_nf
  have hx1 := ne_one_of_norm_lt_one hx
  calc ∑' k : ℕ, ((∑ i ∈ range (k + 1), (1 : ℂ) ^ i) * (∑ j ∈ range (k + 1), (1 : ℂ) ^ j) * x ^ k)
      = ∑' k : ℕ, ((k + 1 : ℂ) ^ 2) * x ^ k := tsum_congr hsimp
    _ = (1 + x) / (1 - x) ^ 3 := tsum_succ_sq_mul_geometric hx
    _ = (1 - x ^ 2) / (1 - x) ^ 4 := by
        have : 1 - x ^ 2 = (1 - x) * (1 + x) := by ring
        rw [this]; field_simp [hx1]

end Scratch
