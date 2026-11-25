module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowFixesComplementOfIsotropic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowMatrixMajorants
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajorantConjugateTransfer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LminorSubmatrixCastSucc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.RankOneBoostIsometries
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.BoostLowerBounds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowDomainCriterionHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowMatMulVec

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowMinimumLowerBoundHolds, ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.TwoSidedBoostBounds

-- ===== clump member: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowMinimumLowerBoundHolds =====
-- clump-header: {"m": "ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowMinimumLowerBoundHolds", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowFixesComplementOfIsotropic\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowMatrixMajorants\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajorantConjugateTransfer\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ImaginaryMajorants\n\n"}
section -- clump:auto
section
@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace ImaginaryMajorants

open MajorantConjugateTransfer FlowMatrixMajorants RankOneBoostIsometries BoostLowerBounds

variable {r : ℕ} (X : Data E r)

theorem jp_col {z : Frame X.Ψ r} (hz : z ∈ X.dom) (τ : X.Ψ) (d : Fin X.p0) :
    X.jp z τ (X.colP z τ d) = X.colP z τ d := by
  have hP : X.ppos z τ (X.colP z τ d) = X.colP z τ d := by
    have h := X.ppos_eq_of z τ (X.gramPos_det_ne hz τ) (X.colP z τ d)
      (fun a => if a = d then 1 else 0) (fun b => by
        rw [show (∑ a, (if a = d then (1 : ℂ) else 0) • col (mat z τ) (Fin.castLE X.p0_le a)) =
          X.colP z τ d by simp [Data.colP]]
        rw [sub_self, hermC_zero_left])
    rw [h]
    simp [Data.colP]
  simp only [Data.jp, hP]
  funext k
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem maj_imag_eq {z : Frame X.Ψ r} (hz : z ∈ X.dom) (ξ : Fin r → E) (b : X.Ψ → ℝ)
    (hy : X.flow ξ (fun τ => I * (b τ : ℂ)) z ∈ X.dom) (τ : X.Ψ)
    (hee : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0) (he0 : Data.emb τ.1 ξ ≠ 0)
    (hq : 0 < 1 + X.c τ * b τ * X.maj z τ (Data.emb τ.1 ξ)) (w : Fin r → ℂ) :
    X.maj (X.flow ξ (fun τ => I * (b τ : ℂ)) z) τ w = X.maj z τ (Matrix.mulVec
      (boost X τ (Data.emb τ.1 ξ) (X.jp z τ (Data.emb τ.1 ξ)) (X.maj z τ (Data.emb τ.1 ξ))
        (Real.sqrt (1 + X.c τ * b τ * X.maj z τ (Data.emb τ.1 ξ)))⁻¹) w) := by
  set e := Data.emb τ.1 ξ with he_def
  obtain ⟨hm, hff, hef, hfe⟩ := plane_facts X τ hz hee he0
  set f := X.jp z τ e with hf_def
  set m := X.maj z τ e with hm_def
  set q := 1 + X.c τ * b τ * m with hq_def
  set σ := Real.sqrt q with hσ_def
  have hσ : 0 < σ := Real.sqrt_pos.mpr hq
  have hσ2 : σ ^ 2 = q := Real.sq_sqrt hq.le
  set T := X.flowMat ξ τ (I * (b τ : ℂ))
  have hT : ∀ v, Matrix.mulVec T v = v + (((X.c τ * b τ : ℝ) : ℂ) * hermC τ.1 X.Gm v e) • e := by
    intro v
    rw [Data.flowMat_mulVec]
    congr 2
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  have hcb : X.c τ * b τ = (σ ^ 2 - 1) / m := by
    rw [hσ2, hq_def]; field_simp; ring
  set B := boost X τ e f m σ
  set B' := boost X τ e f m σ⁻¹
  set P := X.ppos z τ e with hP_def
  set γ : Fin X.p0 → ℂ := fun j => ∑ b, hermC τ.1 X.Gm e (X.colP z τ b) * (X.gramPos z τ)⁻¹ b j
  have hPsum : P = ∑ j, γ j • X.colP z τ j := rfl
  have hPef : P = (1 / 2 : ℂ) • (e + f) := by
    funext k
    simp only [hf_def, Data.jp, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul, ← hP_def]
    ring
  have hPe : hermC τ.1 X.Gm P e = (m / 2 : ℝ) := by
    rw [hPef, hC_smul_left, hC_add_left, hee, hfe]; push_cast; ring
  have hPf : hermC τ.1 X.Gm P f = (m / 2 : ℝ) := by
    rw [hPef, hC_smul_left, hC_add_left, hef, hff]; push_cast; ring
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hσC : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
  have hcol : ∀ d, Matrix.mulVec T (X.colP z τ d) = X.colP (X.flow ξ (fun τ => I * (b τ : ℂ)) z) τ d := by
    intro d
    rw [show X.colP (X.flow ξ (fun τ => I * (b τ : ℂ)) z) τ d = col (mat (X.flow ξ (fun τ => I * (b τ : ℂ)) z) τ) (Fin.castLE X.p0_le d) from rfl, Data.col_flow]
    rfl
  have hzf : ∀ d, hermC τ.1 X.Gm (X.colP z τ d) f = hermC τ.1 X.Gm (X.colP z τ d) e := by
    intro d; rw [hf_def, ← X.hermC_jp_left hz, jp_col X hz τ d]

  have hi : ∀ d, Matrix.mulVec T (X.colP z τ d) = Matrix.mulVec B (X.colP z τ d) +
      (((σ - 1) : ℂ) * (2 * hermC τ.1 X.Gm (X.colP z τ d) e / m)) • Matrix.mulVec B P := by
    intro d
    rw [hT, boost_mulVec, boost_mulVec, hzf, hPe, hPf, hPef, hcb]
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    field_simp
    ring
  have hii : ∀ d, Matrix.mulVec B (X.colP z τ d) = Matrix.mulVec T (X.colP z τ d) -
      (((1 - σ⁻¹) : ℂ) * (2 * hermC τ.1 X.Gm (X.colP z τ d) e / m)) • Matrix.mulVec T P := by
    intro d
    rw [hT, hT, boost_mulVec, hzf, hPe, hPef, hcb]
    funext k
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    field_simp
    ring
  have H2 : ∀ a, ∃ L : Fin X.p0 → ℂ, X.colP (X.flow ξ (fun τ => I * (b τ : ℂ)) z) τ a = ∑ c, L c • Matrix.mulVec B (X.colP z τ c) := by
    intro a
    refine ⟨fun j => (if j = a then 1 else 0) +
      ((σ - 1) : ℂ) * (2 * hermC τ.1 X.Gm (X.colP z τ a) e / m) * γ j, ?_⟩
    rw [← hcol, hi, hPsum, Data.mulVec_lin]
    simp only [add_smul, Finset.sum_add_distrib, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, mul_smul, ← Finset.smul_sum]
  have H1 : ∀ c, ∃ K : Fin X.p0 → ℂ, Matrix.mulVec B (X.colP z τ c) = ∑ a, K a • X.colP (X.flow ξ (fun τ => I * (b τ : ℂ)) z) τ a := by
    intro c
    refine ⟨fun j => (if j = c then 1 else 0) -
      ((1 - σ⁻¹) : ℂ) * (2 * hermC τ.1 X.Gm (X.colP z τ c) e / m) * γ j, ?_⟩
    rw [hii, hPsum, Data.mulVec_lin]
    simp only [hcol, sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, mul_smul, ← Finset.smul_sum]
  have hmt := maj_transfer X hz hy τ B B' (boost_comp X τ hm hee hff hef hfe hσ)
    (boost_isom X τ hm hee hff hef hfe hσ) H1 H2 w
  exact hmt

theorem maj_imag_flow {z : Frame X.Ψ r} (hz : z ∈ X.dom) (ξ : Fin r → E) (b : X.Ψ → ℝ)
    (hy : X.flow ξ (fun τ => I * (b τ : ℂ)) z ∈ X.dom) (τ : X.Ψ)
    (hee : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0) (he0 : Data.emb τ.1 ξ ≠ 0)
    (hq : 0 < 1 + X.c τ * b τ * X.maj z τ (Data.emb τ.1 ξ)) (w : Fin r → ℂ) :
    min (1 + X.c τ * b τ * X.maj z τ (Data.emb τ.1 ξ)) (1 + X.c τ * b τ * X.maj z τ (Data.emb τ.1 ξ))⁻¹ *
      X.maj z τ w ≤ X.maj (X.flow ξ (fun τ => I * (b τ : ℂ)) z) τ w := by
  rw [maj_imag_eq X hz ξ b hy τ hee he0 hq w]
  have hσ : 0 < Real.sqrt (1 + X.c τ * b τ * X.maj z τ (Data.emb τ.1 ξ)) := Real.sqrt_pos.2 hq
  have h := boost_lower (X := X) (z := z) (τ := τ) (e := Data.emb τ.1 ξ) hz hee he0 hσ w
  rwa [Real.sq_sqrt hq.le] at h

end ImaginaryMajorants

end ReciprocityTheory.ChartRestriction.G.FD
end
end

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex MajorantConjugateTransfer FlowMatrixMajorants ImaginaryMajorants
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem majorant_realFlow_transfer {r : ℕ} (X : Data E r) (ξ : Fin r → E) (t : X.Ψ → ℝ) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) (hz : X.flow ξ (fun τ => (t τ : ℂ)) x ∈ X.dom) (τ : X.Ψ)
    (hiso : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0) (w : Fin r → ℂ) :
    X.maj (X.flow ξ (fun τ => (t τ : ℂ)) x) τ w =
      X.maj x τ (Matrix.mulVec (X.flowMat ξ τ (-(t τ : ℂ))) w) := by

  have hcol : ∀ c, Matrix.mulVec (X.flowMat ξ τ (t τ : ℂ)) (X.colP x τ c) =
      X.colP (X.flow ξ (fun τ => (t τ : ℂ)) x) τ c := by
    intro c
    unfold Data.colP
    rw [Data.col_flow]
  refine maj_transfer (hx := hx) (hy := hz) (τ := τ) (g := X.flowMat ξ τ (t τ : ℂ))
    (g' := X.flowMat ξ τ (-(t τ : ℂ))) (hgg' := fun w => flowMat_inv (hiso := hiso) (a := _) (w := w))
    (hiso := fun u v => flowMat_isom_real (hiso := hiso) (t := t τ) (u := u) (v := v))
    (H1 := ?_) (H2 := ?_) (w := w)
  · intro c
    refine ⟨fun a => if a = c then 1 else 0, ?_⟩
    rw [hcol c]
    simp [ite_smul]
  · intro a
    refine ⟨fun c => if c = a then 1 else 0, ?_⟩
    simp [ite_smul, hcol]

end ReciprocityTheory.ChartRestriction.G.FD
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowMinimumLowerBoundHolds =====

-- ===== clump member: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.TwoSidedBoostBounds =====
-- clump-header: {"m": "ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.TwoSidedBoostBounds", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LminorSubmatrixCastSucc\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.RankOneBoostIsometries\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.BoostLowerBounds\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowDomainCriterionHolds\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowFixesComplementOfIsotropic\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowMatrixMajorants\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowMinimumLowerBoundHolds\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ImaginaryMajorants\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajorantConjugateTransfer\n\n"}
section -- clump:auto
@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex MajorantConjugateTransfer FlowMatrixMajorants RankOneBoostIsometries BoostLowerBounds ImaginaryMajorants
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace TwoSidedBoostBounds

variable {r : ℕ} (X : Data E r)

theorem boost_upper (τ : X.Ψ) {z : Frame X.Ψ r} (hz : z ∈ X.dom) {e : Fin r → ℂ}
    (hee : hermC τ.1 X.Gm e e = 0) (he0 : e ≠ 0) {σ : ℝ} (hσ : 0 < σ) (w : Fin r → ℂ) :
    X.maj z τ (Matrix.mulVec (boost X τ e (X.jp z τ e) (X.maj z τ e) σ⁻¹) w) ≤
      max (σ ^ 2) (σ ^ 2)⁻¹ * X.maj z τ w := by
  have hσ' : 0 < σ⁻¹ := inv_pos.2 hσ
  have ha : 0 < σ ^ 2 := by positivity
  have hl := BoostLowerBounds.boost_lower (X := X) (τ := τ) (z := z) hz hee he0 hσ'
    (Matrix.mulVec (boost X τ e (X.jp z τ e) (X.maj z τ e) σ⁻¹) w)
  simp only [inv_inv] at hl
  obtain ⟨hm, hff, hef, hfe⟩ := BoostLowerBounds.plane_facts (X := X) (τ := τ) (z := z) hz hee he0
  rw [RankOneBoostIsometries.boost_comp X τ hm hee hff hef hfe hσ] at hl
  simp only [inv_pow, inv_inv] at hl
  have hmm : max (σ ^ 2) (σ ^ 2)⁻¹ * min (σ ^ 2)⁻¹ (σ ^ 2) = 1 := by
    rcases le_total (σ ^ 2) (σ ^ 2)⁻¹ with h | h
    · rw [max_eq_right h, min_eq_right h, inv_mul_cancel₀ ha.ne']
    · rw [max_eq_left h, min_eq_left h, mul_inv_cancel₀ ha.ne']
  have hM : 0 ≤ max (σ ^ 2) (σ ^ 2)⁻¹ := le_max_of_le_left ha.le
  calc X.maj z τ (Matrix.mulVec (boost X τ e (X.jp z τ e) (X.maj z τ e) σ⁻¹) w)
      = max (σ ^ 2) (σ ^ 2)⁻¹ * (min (σ ^ 2)⁻¹ (σ ^ 2) *
          X.maj z τ (Matrix.mulVec (boost X τ e (X.jp z τ e) (X.maj z τ e) σ⁻¹) w)) := by
        rw [← mul_assoc, hmm, one_mul]
    _ ≤ max (σ ^ 2) (σ ^ 2)⁻¹ * X.maj z τ w := mul_le_mul_of_nonneg_left hl hM

alias c_pos := _root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.c_pos

theorem maj_two_sided {x : Frame X.Ψ r} (hx : x ∈ X.dom) {ξ : Fin r → E} (hξ : X.IsIso ξ)
    (s : X.Ψ → ℂ) (hy : X.flow ξ s x ∈ X.dom) (τ : X.Ψ) (w : Fin r → ℂ) :
    0 < 1 + X.c τ * (s τ).im * X.maj x τ (Data.emb τ.1 ξ) ∧
    min (1 + X.c τ * (s τ).im * X.maj x τ (Data.emb τ.1 ξ))
        (1 + X.c τ * (s τ).im * X.maj x τ (Data.emb τ.1 ξ))⁻¹ /
        (1 + X.c τ * |(s τ).re| * X.maj x τ (Data.emb τ.1 ξ)) ^ 2 * X.maj x τ w ≤
      X.maj (X.flow ξ s x) τ w ∧
    X.maj (X.flow ξ s x) τ w ≤ max (1 + X.c τ * (s τ).im * X.maj x τ (Data.emb τ.1 ξ))
        (1 + X.c τ * (s τ).im * X.maj x τ (Data.emb τ.1 ξ))⁻¹ *
        (1 + X.c τ * |(s τ).re| * X.maj x τ (Data.emb τ.1 ξ)) ^ 2 * X.maj x τ w := by
  obtain ⟨_, hξξ, hξ0⟩ := hξ
  have hiso : ∀ τ : X.Ψ, hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0 := fun τ => by
    rw [hermC_emb, hξξ, map_zero]
  have he0 : ∀ τ : X.Ψ, Data.emb τ.1 ξ ≠ 0 := fun τ h => hξ0 (funext fun a => by
    have := congrFun h a
    simpa [Data.emb] using this)
  have hIsoV : X.IsIsoV (fun τ => Data.emb τ.1 ξ) := fun τ => ⟨hiso τ, he0 τ⟩
  have hm0 : 0 ≤ X.maj x τ (Data.emb τ.1 ξ) := MajorantConjugateTransfer.maj_nonneg X hx τ _
  have hc0 : 0 ≤ X.c τ := (c_pos X τ).le
  have hyd : X.flow ξ (fun τ => ((s τ).re : ℂ)) x ∈ X.dom :=
    ((flowDomainCriterion_holds r X (fun τ => Data.emb τ.1 ξ) hIsoV x hx (fun τ => ((s τ).re : ℂ))).1).2
      (fun τ => by simp)
  have hsplit := flow_split (X := X) (ξ := ξ) hiso s x
  have hyd2 : X.flow ξ (fun τ => I * ((s τ).im : ℂ)) (X.flow ξ (fun τ => ((s τ).re : ℂ)) x) ∈ X.dom :=
    hsplit ▸ hy
  have hmy : X.maj (X.flow ξ (fun τ => ((s τ).re : ℂ)) x) τ (Data.emb τ.1 ξ) =
      X.maj x τ (Data.emb τ.1 ξ) := by
    rw [majorant_realFlow_transfer X ξ (fun τ => (s τ).re) hx hyd τ (hiso τ) (Data.emb τ.1 ξ),
      Data.flow_fix (X := X) (τ := τ) (ξ := ξ) _ _ (hiso τ)]
  have hq : 0 < 1 + X.c τ * (s τ).im * X.maj x τ (Data.emb τ.1 ξ) := by
    have h := ((flowDomainCriterion_holds r X (fun τ => Data.emb τ.1 ξ) hIsoV x hx s).1).1 hy τ
    simp only [Data.ttV, div_div_eq_mul_div, div_one] at h
    have e1 : (s τ).im * (X.c τ * X.maj x τ (Data.emb τ.1 ξ)) =
        X.c τ * (s τ).im * X.maj x τ (Data.emb τ.1 ξ) := by ring
    linarith
  have hq' : 0 < 1 + X.c τ * (s τ).im *
      X.maj (X.flow ξ (fun τ => ((s τ).re : ℂ)) x) τ (Data.emb τ.1 ξ) := by
    rw [hmy]; exact hq
  have hlow := ImaginaryMajorants.maj_imag_flow (X := X) hyd ξ (fun τ => (s τ).im) hyd2 τ (hiso τ) (he0 τ) hq' w
  have heq := ImaginaryMajorants.maj_imag_eq (X := X) hyd ξ (fun τ => (s τ).im) hyd2 τ (hiso τ) (he0 τ) hq' w
  have hsq : 0 < Real.sqrt (1 + X.c τ * (s τ).im *
      X.maj (X.flow ξ (fun τ => ((s τ).re : ℂ)) x) τ (Data.emb τ.1 ξ)) := Real.sqrt_pos.2 hq'
  have hup := boost_upper X τ hyd (hiso τ) (he0 τ) hsq w
  rw [Real.sq_sqrt hq'.le] at hup
  simp only [hmy] at hlow heq hup
  have hyw := majorant_realFlow_transfer X ξ (fun τ => (s τ).re) hx hyd τ (hiso τ) w
  have hup1 := FlowMatrixMajorants.maj_flow_le (X := X) (τ := τ) (ξ := ξ) hx (-(s τ).re) w
  simp only [Complex.ofReal_neg, abs_neg] at hup1
  have hlo1 := FlowMatrixMajorants.maj_flow_le (X := X) (τ := τ) (ξ := ξ) hx ((s τ).re)
    (Matrix.mulVec (X.flowMat ξ τ (-((s τ).re : ℂ))) w)
  rw [FlowMatrixMajorants.flowMat_inv (X := X) (τ := τ) (ξ := ξ) (hiso τ)] at hlo1
  rw [← hyw] at hup1 hlo1
  have hP : 0 < (1 + X.c τ * |(s τ).re| * X.maj x τ (Data.emb τ.1 ξ)) ^ 2 := by positivity
  have hmin0 : 0 ≤ min (1 + X.c τ * (s τ).im * X.maj x τ (Data.emb τ.1 ξ))
      (1 + X.c τ * (s τ).im * X.maj x τ (Data.emb τ.1 ξ))⁻¹ := le_min hq.le (inv_nonneg.2 hq.le)
  have hmax0 : 0 ≤ max (1 + X.c τ * (s τ).im * X.maj x τ (Data.emb τ.1 ξ))
      (1 + X.c τ * (s τ).im * X.maj x τ (Data.emb τ.1 ξ))⁻¹ := le_max_of_le_left hq.le
  have hdiv : X.maj x τ w / (1 + X.c τ * |(s τ).re| * X.maj x τ (Data.emb τ.1 ξ)) ^ 2 ≤
      X.maj (X.flow ξ (fun τ => ((s τ).re : ℂ)) x) τ w := by
    rw [div_le_iff₀ hP, mul_comm]
    exact hlo1
  rw [hsplit]
  refine ⟨hq, ?_, ?_⟩
  · calc _ = min (1 + X.c τ * (s τ).im * X.maj x τ (Data.emb τ.1 ξ))
          (1 + X.c τ * (s τ).im * X.maj x τ (Data.emb τ.1 ξ))⁻¹ *
          (X.maj x τ w / (1 + X.c τ * |(s τ).re| * X.maj x τ (Data.emb τ.1 ξ)) ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hdiv hmin0
      _ ≤ _ := hlow
  · rw [heq]
    calc _ ≤ _ := hup
      _ ≤ _ := mul_le_mul_of_nonneg_left hup1 hmax0
      _ = _ := by ring

end TwoSidedBoostBounds

end ReciprocityTheory.ChartRestriction.G.FD
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.TwoSidedBoostBounds =====
