module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.MeasBAll
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.GOfPrime
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.HaarIdx
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.TensTopRing
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ParabolicImageOfFrameBasis
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataInst
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.StKHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.TwoPrimes
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.StRedOfSplitLat
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.CharZeroAdicCompletion
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ReductionImageOfAdaptedMod
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.ThetaEpsCases
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.MatRMulMatC
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SecondCoordsCongruentMod
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.DenomHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.LatBasisAllOfParts
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SplitLatticeBasisExists

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.MassDataIndicesOfSteps, Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.LocOpenHolds, Formalism.PeriodIntegrals.OrbitalBoundsConclusion.MassDataIndices, Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXRed

-- ===== clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.MassDataIndicesOfSteps =====
-- clump-header: {"m": "Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.MassDataIndicesOfSteps", "h": "module\n\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.MeasBAll\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.GOfPrime\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.HaarIdx\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.TensTopRing\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
open scoped ENNReal

theorem massDataIndices_of (hA : MeasAAll) (hB : MeasBAll) :
    ∀ {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I)
      (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf) (u u' : D.what₂.Word)
      (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (L : Formalism.L2.SG.TypedSets.LocIn (Formalism.L2.SG.TypedSets.TypX X))
      (A : Formalism.L2.SG.TypedSets.AnIn), Formalism.L2.SG.TypedSets.InIndicesAt X hb hK FdN FdN' u u' X0 L A := by
  intro D X hb hK FdN FdN' u u' X0 L A hX p
  obtain ⟨i, hi, hi0, hμi⟩ := hA X hb hK FdN FdN' u u' hX p
  obtain ⟨j, hj, hj0, hμj, hB0, hBt⟩ := hB X hb hK FdN FdN' u u' hX p
  refine ⟨?_, ?_⟩
  · show (X.measG.μGv p.1 (KvX X p)).toReal =
      (ggC D.R.rS D.R.k (gOf p) : ℝ) / ((nnC D.R.rS D.R.k (gOf p) : ℝ) * (ukC D.R.k (gOf p) : ℝ)) *
        (X.measG.μGv p.1 (KppX X hb p)).toReal
    have h1 : (muP X p (KvX X p)).toReal = (i : ℝ) * (muP X p (KppX X hb p)).toReal := by
      rw [hμi, ENNReal.toReal_mul, ENNReal.toReal_natCast]
    rw [← hi, mul_div_assoc, div_self hi0, mul_one]
    exact h1
  · show (X.measG.μGv p.1 (KnatX X u p)).toReal / (X.measG.μGv p.1 (KvX X p)).toReal =
      (glkC D.R.k (gOf p) : ℝ) * (nnC D.R.rS D.R.k (gOf p) : ℝ) / (ggC D.R.rS D.R.k (gOf p) : ℝ)
    have h1 : (muP X p (KvX X p)).toReal = (j : ℝ) * (muP X p (KnatX X u p)).toReal := by
      rw [hμj, ENNReal.toReal_mul, ENNReal.toReal_natCast]
    have hpos : (muP X p (KnatX X u p)).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hB0, hBt⟩
    show (muP X p (KnatX X u p)).toReal / (muP X p (KvX X p)).toReal = _
    rw [h1, ← hj]
    rcases eq_or_ne (j : ℝ) 0 with h0 | h0
    · simp [h0]
    · rw [mul_comm (j : ℝ) (muP X p (KnatX X u p)).toReal, mul_comm (j : ℝ), div_mul_eq_div_div,
        div_self hpos, div_mul_eq_div_div, div_self hj0]

def LocAll : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (_hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
    (u u' : D.what₂.Word), HypX X hb FdN FdN' u u' → ∀ p : TypX X,
      StTop X p ∧ StK X p ∧ StRed X p ∧ StImA X hb p ∧ StImB X u p

theorem massDataIndices_of_haarIdx_redIdx_locAll (hH : HaarIdx) (hR : RedIdx) (hL : LocAll) :
    ∀ {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I)
      (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf) (u u' : D.what₂.Word)
      (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (L : Formalism.L2.SG.TypedSets.LocIn (Formalism.L2.SG.TypedSets.TypX X))
      (A : Formalism.L2.SG.TypedSets.AnIn), Formalism.L2.SG.TypedSets.InIndicesAt X hb hK FdN FdN' u u' X0 L A :=
  massDataIndices_of
    (fun X hb hK FdN FdN' u u' hX p =>
      let h := hL X hb hK FdN FdN' u u' hX p
      measA_of X hb hH hR p h.1 h.2.1 h.2.2.1 h.2.2.2.1)
    (fun X hb hK FdN FdN' u u' hX p =>
      let h := hL X hb hK FdN FdN' u u' hX p
      measB_of X hH hR u p h.1 h.2.1 h.2.2.1 h.2.2.2.2)

theorem massDataIndices_of_locAll (hL : LocAll) :
    ∀ {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I)
      (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf) (u u' : D.what₂.Word)
      (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (L : Formalism.L2.SG.TypedSets.LocIn (Formalism.L2.SG.TypedSets.TypX X))
      (A : Formalism.L2.SG.TypedSets.AnIn), Formalism.L2.SG.TypedSets.InIndicesAt X hb hK FdN FdN' u u' X0 L A := by
  have hH : HaarIdx := by
    exact haarIdx
  have hR : RedIdx := by
    exact redIdx
  intro D X
  exact massDataIndices_of_haarIdx_redIdx_locAll hH hR hL X

def LocOpen : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (_hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
    (u u' : D.what₂.Word), HypX X hb FdN FdN' u u' → ∀ p : TypX X,
      StK X p ∧ StRed X p ∧ StImA X hb p ∧ StImB X u p

theorem massDataIndices_of_locOpen (hL : LocOpen) :
    ∀ {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I)
      (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf) (u u' : D.what₂.Word)
      (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (L : Formalism.L2.SG.TypedSets.LocIn (Formalism.L2.SG.TypedSets.TypX X))
      (A : Formalism.L2.SG.TypedSets.AnIn), Formalism.L2.SG.TypedSets.InIndicesAt X hb hK FdN FdN' u u' X0 L A := by
  exact massDataIndices_of_locAll (fun X hb hK FdN FdN' u u' hX p => ⟨stTop X p, hL X hb hK FdN FdN' u u' hX p⟩)

end MassDataIdxSteps
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.MassDataIndicesOfSteps =====

-- ===== clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.LocOpenHolds =====
-- clump-header: {"m": "Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.LocOpenHolds", "h": "module\n\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.MassDataIndicesOfSteps\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.LatBasisAllHolds\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ParabolicImageOfFrameBasis\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ReductionImageEveryPlace\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SecondCoordsAdaptedColumn\nimport Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.StKHolds\nimport Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.TwoPrimes\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto

section
@[expose] public section

noncomputable section

namespace MassDataIdxSteps

open Formalism.L2.SG.TypedSets Formalism.BasicNotions Formalism.L2.SG.HidaSetting

theorem stRed_of_embP {D : D7} (X : HidaSetting D) (p : TypX X) (hE : EmbP X p) : StRed X p :=
  stRed_of_emb X p hE (_root_.MassDataIdxSteps.latBasisAll_holds' X p)

end MassDataIdxSteps
end
end
end

section
section -- clump:auto
@[expose] public section

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxRed MassDataIdxSpl Matrix
  MassDataIdxFrA
open scoped TensorProduct

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X)

theorem oEpSplit_holds (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p) (hθ : IsSplitEquiv X p θ) :
    OEpSplit X p θ := by
  have hone : θ.symm (1, 1) = 1 := by rw [Prod.mk_one_one, map_one]
  have hsub : ∀ a b : FpX X p × FpX X p, θ.symm (a - b) = θ.symm a - θ.symm b := fun a b => map_sub _ _ _
  have hm : 1 - epsP X p ∈ OEp X p := imA_OEp_sub X p (imA_OEp_one X p) (imA_eps_mem X p)
  rcases PIW.MassDataColumns.theta_eps_cases X p θ hθ with h | h
  · have e1 : θ.symm (1, 0) = epsP X p := by rw [← h, AlgEquiv.symm_apply_apply]
    have e2 : θ.symm (0, 1) = 1 - epsP X p := by
      rw [← hone, ← e1, ← hsub]; congr 1; ext <;> simp
    exact ⟨e1 ▸ imA_eps_mem X p, e2 ▸ hm⟩
  · have e1 : θ.symm (0, 1) = epsP X p := by rw [← h, AlgEquiv.symm_apply_apply]
    have e2 : θ.symm (1, 0) = 1 - epsP X p := by
      rw [← hone, ← e1, ← hsub]; congr 1; ext <;> simp
    exact ⟨e2 ▸ hm, e1 ▸ imA_eps_mem X p⟩

def StAdaptBasisA : Prop :=
  ∃ θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p, IsSplitEquiv X p θ ∧
    ∃ Q : GL (IdxD D) (FpX X p), LatBasis X p θ (reindex₂ X p Q) ∧ AdaptA X p θ Q

theorem reduction_image_of_basis (hb : AdBridgeIso X.B.I) (h : StAdaptBasisA X p) : LevelReductionImage X hb p := by
  obtain ⟨θ, hθ, Q, hL, hA⟩ := h
  exact reduction_image_of_adapted_mod X p hb latCoreX_holds ⟨θ, hθ, oEpSplit_holds X p θ hθ, Q, hL, hA⟩

end Loc

end MassDataIdxSteps
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ReductionImageOfBasis =====

section -- clump:auto
@[expose] public section

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge

theorem stAdaptBasisA_holds {D : D7} (X : HidaSetting D) (p : TypX X) : StAdaptBasisA X p :=
  adaptA_holds X p

theorem reduction_image_every_place {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (p : TypX X) : LevelReductionImage X hb p :=
  reduction_image_of_basis X p hb (stAdaptBasisA_holds X p)

end MassDataIdxSteps
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ReductionImageEveryPlace =====
end

section
@[expose] public section

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxRed MassDataIdxSpl Matrix
  MassDataIdxFrA MassDataIdxAdA PIW.MassDataColumns
open scoped TensorProduct

section Loc

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (p : TypX X)
  (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p) (Q : GL (IdxD D) (FpX X p))

theorem firstCoords_adapted_column (c : GL (IdxD D) (OvA X p))
    (hc : ((glK (OvA X p) c : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p)) = adqC X hb u p θ Q)
    (v : Fin X.B.I.n → TpX X p) (t : IdxD D) (hv : crd1 X p θ Q v = adqCol X hb u p θ Q t) :
    crd1 X p θ (Q * glK (OvA X p) c) v = Pi.single t 1 := by
  have e1 : crd1 X p θ (Q * glK (OvA X p) c) v =
      (((glK (OvA X p) c)⁻¹ : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p)) *ᵥ
        crd1 X p θ Q v := by
    simp only [crd1, _root_.mul_inv_rev, Units.val_mul, Matrix.mulVec_mulVec]
  have e2 : adqCol X hb u p θ Q t =
      ((glK (OvA X p) c : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p)) *ᵥ
        Pi.single t 1 := by
    rw [hc]
    funext i
    simp [adqC, Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [e1, hv, e2, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem secondCoords_adapted_column (c : GL (IdxD D) (OvA X p))
    (hc : ((glK (OvA X p) c : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p)) = adqC X hb u p θ Q)
    (v : Fin X.B.I.n → TpX X p) (t : IdxD D) :
    crd2 X p θ (Q * glK (OvA X p) c) v t = crd2 X p θ Q v ⬝ᵥ adqCol X hb u p θ Q t := by
  have e1 : crd2 X p θ (Q * glK (OvA X p) c) v =
      (((glK (OvA X p) c : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p)))ᵀ *ᵥ
        crd2 X p θ Q v := by
    simp only [crd2, Units.val_mul, Matrix.transpose_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [e1, hc]
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, adqC]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem frame_castSucc_vector_eq (a : Fin D.R.rS) :
    F0 (frameOf X u) (Fin.castSucc a) = crdOf X.B.I X.ιE X.bas (X.eX a) := by
  first
  | simp [F0, frameOf]

theorem frame_last_vector_eq : F0 (frameOf X u) (Fin.last D.R.rS) = crdOf X.B.I X.ιE X.bas (X.zu u) := by
  first
  | simp [F0, frameOf]

end Loc

theorem stAdaptQ_holds {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (p : TypX X) :
    StAdaptQ X u p := by
  obtain ⟨θ, hθ, hε⟩ := exists_split_eps X p
  obtain ⟨Q, hL⟩ := exists_GL_latBasis_of_isSplitEquiv X p θ hθ
  obtain ⟨c, hc⟩ := adq_gl X hb u p θ Q hθ hε hL
  have hτ := (adq_tau_inv X hb u p θ Q hθ hL).2
  refine ⟨θ, hθ, Q * glK (OvA X p) c, Fin.lastCases (adqTau X u p θ Q) (fun _ => 1), ?_, ?_, ?_,
    latBasis_mulGL X p θ Q hL c⟩
  · intro b
    induction b using Fin.lastCases with
    | last => dsimp only; rw [Fin.lastCases_last]; exact hτ
    | cast a => dsimp only; rw [Fin.lastCases_castSucc]; exact one_ne_zero
  · intro b
    show crd1 X p θ (Q * glK (OvA X p) c) _ = _
    induction b using Fin.lastCases with
    | last =>
      rw [frame_last_vector_eq]
      have hp : pe (k := D.R.k) (Fin.last D.R.rS) = zI := by simp [pe]
      rw [hp]
      exact firstCoords_adapted_column X hb u p θ Q c hc _ zI rfl
    | cast a =>
      rw [frame_castSucc_vector_eq]
      have hp : pe (k := D.R.k) (Fin.castSucc a) = Sum.inl a := by simp [pe]
      rw [hp]
      exact firstCoords_adapted_column X hb u p θ Q c hc _ (Sum.inl a) rfl
  · intro b
    show crd2 X p θ (Q * glK (OvA X p) c) _ = _
    funext t
    rw [secondCoords_adapted_column X hb u p θ Q c hc]
    induction b using Fin.lastCases with
    | last =>
      rw [frame_last_vector_eq]
      dsimp only
      rw [Fin.lastCases_last]
      have hp : pf (k := D.R.k) (Fin.last D.R.rS) = zI := by simp [pf]
      rw [hp]
      rcases t with a | ((i | v) | c')
      · rw [show adqCol X hb u p θ Q (Sum.inl a) = crd1 X p θ Q (adqE X p a) from rfl]
        rw [adq_ze X u p θ Q hθ]
        simp [zI]
      · rw [show adqCol X hb u p θ Q (Sum.inr (Sum.inl (Sum.inl i))) = adqProj X u p θ Q
          (crd1 X p θ Q (adqM X hb u p *ᵥ PI.FinKW.vecV X.B.I p.1 (X.bw i))) from rfl]
        rw [secondCoords_projection_orth X u p θ Q hθ hτ]
        simp [zI]
      · rw [show adqCol X hb u p θ Q (Sum.inr (Sum.inl (Sum.inr v))) = crd1 X p θ Q (adqZ X u p) from rfl]
        have hv : v = () := rfl
        subst hv
        simp [zI, adqTau]
      · rw [show adqCol X hb u p θ Q (Sum.inr (Sum.inr c')) = crd1 X p θ Q (adqF X p (Fin.rev c')) from rfl]
        rw [adq_zf X u p θ Q hθ]
        simp [zI]
    | cast b =>
      rw [frame_castSucc_vector_eq]
      dsimp only
      rw [Fin.lastCases_castSucc]
      have hp : pf (k := D.R.k) (Fin.castSucc b) = Sum.inr (Sum.inr (Fin.rev b)) := by simp [pf]
      rw [hp]
      rcases t with a | ((i | v) | c')
      · rw [show adqCol X hb u p θ Q (Sum.inl a) = crd1 X p θ Q (adqE X p a) from rfl]
        rw [adq_ee X p θ Q u hθ]
        simp
      · rw [show adqCol X hb u p θ Q (Sum.inr (Sum.inl (Sum.inl i))) = adqProj X u p θ Q
          (crd1 X p θ Q (adqM X hb u p *ᵥ PI.FinKW.vecV X.B.I p.1 (X.bw i))) from rfl]
        rw [adq_proj_e X u p θ Q hθ]
        simp
      · rw [show adqCol X hb u p θ Q (Sum.inr (Sum.inl (Sum.inr v))) = crd1 X p θ Q (adqZ X u p) from rfl]
        rw [adq_ez X u p θ Q hθ]
        simp
      · rw [show adqCol X hb u p θ Q (Sum.inr (Sum.inr c')) = crd1 X p θ Q (adqF X p (Fin.rev c')) from rfl]
        rw [adq_ef X p θ Q u hθ]
        by_cases h : c' = Fin.rev b
        · subst h
          simp
        · have h' : b ≠ Fin.rev c' := fun e => h (by rw [e, Fin.rev_rev])
          simp [h, h']

end MassDataIdxSteps
end
end
end

@[expose] public section

namespace MassDataIdxSteps

theorem locOpen_holds : LocOpen := fun X hb _hK _ _ u _ _ p =>
  ⟨stK_holds X p, stRed_of_embP X p (embP_holds X p), stImA_of X hb p (reduction_image_every_place X hb p),
    stImB_of_adaptQ X u p (stAdaptQ_holds X hb u p)⟩

end MassDataIdxSteps
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.LocOpenHolds =====

-- ===== clump member: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.MassDataIndices =====
-- clump-header: {"m": "Formalism.PeriodIntegrals.OrbitalBoundsConclusion.MassDataIndices", "h": "module\n\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataInst\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.LocOpenHolds\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

theorem local_indices_at_instance : ∀ {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf) (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (L : Formalism.L2.SG.TypedSets.LocIn (Formalism.L2.SG.TypedSets.TypX X)) (A : Formalism.L2.SG.TypedSets.AnIn), Formalism.L2.SG.TypedSets.InIndicesAt X hb hK FdN FdN' u u' X0 L A :=
  MassDataIdxSteps.massDataIndices_of_locOpen MassDataIdxSteps.locOpen_holds
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.MassDataIndices =====

-- ===== clump member: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXRed =====
-- clump-header: {"m": "Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXRed", "h": "module\n\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.MeasBAll\npublic import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.MassDataIndices\nimport Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.LatBasisAllHolds\nimport Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ParabolicImageOfFrameBasis\nimport Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ReductionImageEveryPlace\nimport Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SecondCoordsAdaptedColumn\nimport Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.StKHolds\nimport Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.TwoPrimes\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

namespace Formalism.L2.SG.Pf.MassDataX

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets

alias stK_holds := _root_.MassDataIdxSteps.stK_holds

theorem stRed_holds {D : D7} (X : HidaSetting D) (p : TypX X) : MassDataIdxSteps.StRed X p :=
  MassDataIdxSteps.stRed_of_embP X p (MassDataIdxSteps.embP_holds X p)

theorem stImA_holds {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (p : TypX X) :
    MassDataIdxSteps.StImA X hb p :=
  MassDataIdxSteps.stImA_of X hb p (MassDataIdxSteps.reduction_image_every_place X hb p)

theorem stImB_holds {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (p : TypX X) :
    MassDataIdxSteps.StImB X u p :=
  MassDataIdxSteps.stImB_of_adaptQ X u p (MassDataIdxSteps.stAdaptQ_holds X hb u p)

end Formalism.L2.SG.Pf.MassDataX
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXRed =====
