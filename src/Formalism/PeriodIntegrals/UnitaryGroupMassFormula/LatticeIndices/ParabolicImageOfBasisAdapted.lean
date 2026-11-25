module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ParabolicReductionImage
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.StRedOfSplit
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SplitTransport
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.GlRedEqOneIff
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.CardNuGZmod
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.MemSGIffFlags
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.StRedOfParts
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.MemSsubIffFlagC
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.MemSsubIffSG
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.StRedOfCore
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.GOfPrime
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ParabolicImageOfResidueFrame, Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.MemSGIffMap, Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ParabolicImageOfAdapted, Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ParabolicImageOfBasisAdapted

-- ===== clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ParabolicImageOfResidueFrame =====
-- clump-header: {"m": "Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ParabolicImageOfResidueFrame", "h": "module\n\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ParabolicReductionImage\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.StRedOfSplit\nimport Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.GOfPrime\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ParGMapGlRed\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SplitTransport\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.GlRedEqOneIff\n\n"}
section -- clump:auto
section
@[expose] public section

noncomputable section

namespace MassDataIdxStImB

open Matrix Formalism.FourierDecayAlt.S3 MassDataIdxStIm MassDataIdxRed
open Formalism.DoubleCosetMeasures (IsUpUni)

section Lift

variable {R S : Type} [CommRing R] [CommRing S] (π : R →+* S) (hπ : Function.Surjective π)


open Classical in
def lift (s : S) : R := if s = 0 then 0 else if s = 1 then 1 else Function.surjInv hπ s

theorem lift_zero : lift π hπ 0 = 0 := by
  simp [lift]

theorem lift_one [Nontrivial S] : lift π hπ 1 = 1 := by
  simp [lift]

theorem π_lift (s : S) : π (lift π hπ s) = s := by
  unfold lift
  split_ifs with h0 h1
  · rw [h0, map_zero]
  · rw [h1, map_one]
  · exact Function.surjInv_eq hπ s

theorem map_lift {m n : Type} (x : Matrix m n S) : (x.map (lift π hπ)).map π = x := by
  ext i j
  simp only [Matrix.map_apply, π_lift]

end Lift

section Par

variable {A B : Type} [CommRing A] [CommRing B] {r k : ℕ}

theorem isUpUni_map (f : A → B) (h0 : f 0 = 0) (h1 : f 1 = 1) {n : ℕ} {h : Matrix (Fin n) (Fin n) A}
    (hh : IsUpUni h) : IsUpUni (h.map f) := by
  obtain ⟨hu, hd⟩ := hh
  refine ⟨?_, fun a => by simp [Matrix.map_apply, hd a, h1]⟩
  intro i j hij
  simp [Matrix.map_apply, hu hij, h0]

theorem midEmb_map (f : A → B) (h0 : f 0 = 0) (h1 : f 1 = 1) (h : Matrix (Fin k) (Fin k) A) :
    (midEmb h).map f = midEmb (h.map f) := by
  simp only [midEmb, Matrix.fromBlocks_map, Matrix.map_zero f h0, Matrix.map_one f h0 h1]

theorem par_map (f : A → B) (h0 : f 0 = 0) (h1 : f 1 = 1) {P : Matrix (Fin k) (Fin k) A → Prop}
    {P' : Matrix (Fin k) (Fin k) B → Prop} (hPP : ∀ h, P h → P' (h.map f))
    {x : Matrix (Idx r k) (Idx r k) A} (hx : Par P x) : Par P' (x.map f) := by
  obtain ⟨h11, h33, h21, h31, h32, h, hP, h22⟩ := hx
  refine ⟨isUpUni_map f h0 h1 h11, isUpUni_map f h0 h1 h33, ?_, ?_, ?_, h.map f, hPP h hP, ?_⟩
  · show (b21 x).map f = 0
    rw [h21, Matrix.map_zero f h0]
  · show (b31 x).map f = 0
    rw [h31, Matrix.map_zero f h0]
  · show (b32 x).map f = 0
    rw [h32, Matrix.map_zero f h0]
  · show (b22 x).map f = midEmb (h.map f)
    rw [h22, midEmb_map f h0 h1]

variable [Nontrivial B] (π : A →+* B) (hπ : Function.Surjective π)

theorem parG_map_glRed {P : Matrix (Fin k) (Fin k) A → Prop} {P' : Matrix (Fin k) (Fin k) B → Prop}
    (hP : GP P) (hP' : GP P') (hPP : ∀ h, P h → P' (h.map π))
    (hlift : ∀ h, P' h → P (h.map (lift π hπ))) :
    (parG (r := r) hP).map (glRed π) = parG (r := r) hP' := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change Par P' ((glRed π x : GL (Idx r k) B) : Matrix (Idx r k) (Idx r k) B)
    rw [glRed_coe]
    exact par_map π (map_zero π) (map_one π) hPP hx
  · intro hy
    have hy' : Par P' (y : Matrix (Idx r k) (Idx r k) B) := hy
    have hx : Par P ((y : Matrix (Idx r k) (Idx r k) B).map (lift π hπ)) :=
      par_map _ (lift_zero π hπ) (lift_one π hπ) hlift hy'
    refine ⟨Matrix.GeneralLinearGroup.mk'' _ (par_det hP hx), hx, ?_⟩
    apply Units.ext
    rw [glRed_coe]
    exact map_lift π hπ _


end Par

theorem sG_map_glRed {A B : Type} [CommRing A] [IsLocalRing A] [Field B] {r k : ℕ} (π : A →+* B)
    (hπ : Function.Surjective π) : (sG A r k).map (glRed π) = sG B r k := by
  refine parG_map_glRed π hπ _ _ (fun h hh => ?_) (fun h hh => ?_)
  · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact hh.map π
  · refine isUnit_of_map π hπ _ ?_
    rw [RingHom.map_det, RingHom.mapMatrix_apply, map_lift π hπ]
    exact hh

section Grp

theorem map_conj {G Q : Type} [Group G] [Group Q] (f : G →* Q) (H : Subgroup G) (c : G) :
    (H.map (MulAut.conj c).toMonoidHom).map f = (H.map f).map (MulAut.conj (f c)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, map_mul, map_inv]

variable {K Q : Type} [Group K] [Group Q] (ρ : K →* Q) (S' : Subgroup K)

theorem map_sup_ker : (S' ⊔ ρ.ker).map ρ = S'.map ρ := by
  rw [Subgroup.map_sup, (Subgroup.map_eq_bot_iff ρ.ker).2 le_rfl, sup_bot_eq]

theorem mem_sup_ker {x : K} : x ∈ S' ⊔ ρ.ker ↔ ∃ s ∈ S', ∃ κ ∈ ρ.ker, s * κ = x := by
  first
    | exact Subgroup.mem_sup_of_normal_right

theorem map_eq_conj (ψ : K →* Q) (hψ : Function.Surjective ψ) (S' : Subgroup K) (H : Subgroup Q) (c : Q)
    (h : ∀ x, x ∈ S' ↔ c⁻¹ * ψ x * c ∈ H) : S'.map ψ = H.map (MulAut.conj c).toMonoidHom := by
  ext y
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨c⁻¹ * ψ x * c, (h x).1 hx, by group⟩
  · rintro ⟨h', hh', rfl⟩
    obtain ⟨x, hx⟩ := hψ (c * h' * c⁻¹)
    refine ⟨x, (h x).2 ?_, hx⟩
    have e : c⁻¹ * (c * h' * c⁻¹) * c = h' := by group
    rw [hx, e]
    exact hh'

end Grp

end MassDataIdxStImB
end
end
end

@[expose] public section

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxStImB MassDataIdxRed

section Loc

variable {D : D7} (X : HidaSetting D)

abbrev SuX (u : D.what₂.Word) (p : TypX X) : Subgroup (HAp X p) :=
  Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u)

def StSImgB (u : D.what₂.Word) (p : TypX X) : Prop :=
  ∃ K : Subgroup (HAp X p), (K : Set (HAp X p)) = KvX X p ∧
    ∃ ψ : K →* GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p), Function.Surjective ψ ∧
      (∀ x : K, (∀ i j, ((ψ x : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p))
        - 1) i j ∈ Ideal.span {((gOf p : ℕ) : Op X p)}) ↔ (x : HAp X p) ∈ KgX X p) ∧
      ∃ c, ((SuX X u p).comap K.subtype).map ψ = (sG (Op X p) D.R.rS D.R.k).map (MulAut.conj c).toMonoidHom

theorem parabolic_image_of_residue (u : D.what₂.Word) (p : TypX X) (hR : StResZ X p) (hS : StSImgB X u p) :
    ParabolicReductionImage X u p := by
  obtain ⟨π, hπ, hker⟩ := hR
  obtain ⟨K, hK, ψ, hψ, hP, c, hc⟩ := hS
  have : Fact (gOf p).Prime := ⟨gOf_prime X p⟩
  set ρ₀ : K →* GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p)) := (glRed π).comp ψ with hρ₀
  have hker₀ : ∀ x : K, ρ₀ x = 1 ↔ (x : HAp X p) ∈ KgX X p := by
    intro x
    rw [hρ₀, MonoidHom.comp_apply, glRed_eq_one_iff, hker]
    exact hP x
  have hmemK : ∀ y : HAp X p, y ∈ KvX X p → y ∈ K := fun y hy => by
    rw [← SetLike.mem_coe, hK]; exact hy
  refine ⟨K, hK, ρ₀, (glRed_surjective π hπ (isUnit_of_map π hπ)).comp hψ, hker₀,
    (SuX X u p).comap K.subtype ⊔ ρ₀.ker, ?_, le_sup_right, glRed π c, ?_⟩
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨s, hs, κ, hκ, rfl⟩ := (mem_sup_ker ρ₀ _).1 hx
      have hκ' : (κ : HAp X p) ∈ KgX X p := (hker₀ κ).1 hκ
      have hsK : (s : HAp X p) ∈ KvX X p := by rw [← hK]; exact s.2
      have hxK : ((s * κ : K) : HAp X p) ∈ KvX X p := by rw [← hK]; exact (s * κ).2
      exact ⟨hxK, s, κ, hs, hsK, hκ', rfl⟩
    · rintro ⟨hy, s, κ, hs, hsK, hκ, rfl⟩
      refine ⟨⟨s, hmemK s hsK⟩ * ⟨κ, hmemK κ hκ.1⟩, ?_, rfl⟩
      refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right ?_)
      · exact hs
      · rw [MonoidHom.mem_ker, hker₀]; exact hκ
  · rw [map_sup_ker, hρ₀, ← Subgroup.map_map, hc, map_conj,
      sG_map_glRed π hπ]

def StFrameB (u : D.what₂.Word) (p : TypX X) : Prop :=
  ∃ K : Subgroup (HAp X p), (K : Set (HAp X p)) = KvX X p ∧
    ∃ ψ : K →* GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p), Function.Surjective ψ ∧
      (∀ x : K, (∀ i j, ((ψ x : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p))
        - 1) i j ∈ Ideal.span {((gOf p : ℕ) : Op X p)}) ↔ (x : HAp X p) ∈ KgX X p) ∧
      ∃ c, ∀ x : K, (x : HAp X p) ∈ SuX X u p ↔ c⁻¹ * ψ x * c ∈ sG (Op X p) D.R.rS D.R.k

theorem stSImgB_of (u : D.what₂.Word) (p : TypX X) (h : StFrameB X u p) : StSImgB X u p := by
  obtain ⟨K, hK, ψ, hψ, hP, c, hc⟩ := h
  exact ⟨K, hK, ψ, hψ, hP, c, map_eq_conj ψ hψ _ _ c fun x => hc x⟩

theorem parabolic_image_of_residue_frame (u : D.what₂.Word) (p : TypX X) (hR : StResZ X p) (h : StFrameB X u p) :
    ParabolicReductionImage X u p :=
  parabolic_image_of_residue X u p hR (stSImgB_of X u p h)

theorem parabolic_image_of_frame (u : D.what₂.Word) (p : TypX X) (h : StFrameB X u p) : ParabolicReductionImage X u p :=
  parabolic_image_of_residue_frame X u p (stResZ_holds X p) h

end Loc

end MassDataIdxSteps
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ParabolicImageOfResidueFrame =====

-- ===== clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.MemSGIffMap =====
-- clump-header: {"m": "Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.MemSGIffMap", "h": "module\n\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.CardNuGZmod\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.GlRedEqOneIff\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.MemSGIffFlags\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ParGMapGlRed\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace MassDataIdxStIm

open Matrix Formalism.FourierDecayAlt.S3 MassDataIdxRed
open Formalism.DoubleCosetMeasures (IsUpUni)

variable {A B : Type} [CommRing A] [CommRing B] {r k : ℕ}

theorem mem_sG_iff_map (f : A →+* B) (hf : Function.Injective f) (g : GL (Idx r k) A) :
    g ∈ sG A r k ↔ glRed f g ∈ sG B r k := by
  change Par _ (g : Matrix (Idx r k) (Idx r k) A) ↔ Par _ ((glRed f g : GL (Idx r k) B) : Matrix (Idx r k) (Idx r k) B)
  rw [glRed_coe]
  set x : Matrix (Idx r k) (Idx r k) A := (g : Matrix (Idx r k) (Idx r k) A) with hx
  have z0 : ∀ {a : A}, f a = 0 → a = 0 := fun h => hf (by rw [h, map_zero])
  have z1 : ∀ {a : A}, f a = 1 → a = 1 := fun h => hf (by rw [h, map_one])
  constructor
  · intro h
    refine MassDataIdxStImB.par_map f (map_zero f) (map_one f) (fun h hh => ?_) h
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact hh.map f
  · rintro ⟨h11, h33, h21, h31, h32, h, _, h22⟩
    have u11 : IsUpUni (b11 x) :=
      ⟨fun i j hij => z0 (h11.1 hij), fun a => z1 (h11.2 a)⟩
    have u33 : IsUpUni (b33 x) :=
      ⟨fun i j hij => z0 (h33.1 hij), fun a => z1 (h33.2 a)⟩
    have v21 : b21 x = 0 := by ext i j; exact z0 (congrFun (congrFun h21 i) j)
    have v31 : b31 x = 0 := by ext i j; exact z0 (congrFun (congrFun h31 i) j)
    have v32 : b32 x = 0 := by ext i j; exact z0 (congrFun (congrFun h32 i) j)
    have v22 : b22 x = midEmb (Matrix.of fun i j => x (wI i) (wI j)) := by
      ext i j
      have e := congrFun (congrFun h22 i) j
      rcases i with i | i <;> rcases j with j | j
      · rfl
      · exact z0 (by simpa [b22, midEmb] using e)
      · exact z0 (by simpa [b22, midEmb] using e)
      · exact z1 (by simpa [b22, midEmb] using e)
    refine ⟨u11, u33, v21, v31, v32, Matrix.of fun i j => x (wI i) (wI j), ?_, v22⟩
    show IsUnit (Matrix.det _)
    rw [← det_shape u11 u33 v21 v31 v32 _ v22, hx]
    exact (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit

end MassDataIdxStIm
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.MemSGIffMap =====

-- ===== clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ParabolicImageOfAdapted =====
-- clump-header: {"m": "Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ParabolicImageOfAdapted", "h": "module\n\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ParabolicImageOfResidueFrame\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.StRedOfParts\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.GlRedEqOneIff\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.MemSsubIffFlagC\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.MemSGIffMap\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.MemSsubIffSG\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.StRedOfCore\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxRed MassDataIdxSpl Matrix

section Loc

variable {D : D7} (X : HidaSetting D)

def StAdaptB (u : D.what₂.Word) (p : TypX X) : Prop :=
  ∃ θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p, IsSplitEquiv X p θ ∧
    ∃ (e : Fin X.B.I.n ≃ Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Q : GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p))
      (l : Fin (D.R.rS + 1) → FpX X p), (∀ b, l b ≠ 0) ∧
      (∀ b, ((Q⁻¹ : GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) *ᵥ
        (pr1 θ (ratV (F := X.B.I.F) (FpX X p) (F0 (frameOf X u) b)) ∘ e.symm) = Pi.single (pe b) 1) ∧
      (∀ b, (Q : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p))ᵀ *ᵥ ((Matrix.reindex e e (jm1 X.B.I.J θ))ᵀ *ᵥ
        (pr2 θ (ratV (F := X.B.I.F) (FpX X p) (F0 (frameOf X u) b)) ∘ e.symm)) = l b • Pi.single (pf b) 1) ∧
      ∃ K : Subgroup (HAp X p), (K : Set (HAp X p)) = KvX X p ∧
        ∃ ψ : K →* GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p), Function.Surjective ψ ∧
          (∀ x : K, (∀ i j, ((ψ x : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p))
            - 1) i j ∈ Ideal.span {((gOf p : ℕ) : Op X p)}) ↔ (x : HAp X p) ∈ KgX X p) ∧
          ∀ x : K, ((glRed (algebraMap (Op X p) (FpX X p)) (ψ x) : GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) =
            ((Q⁻¹ : GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) * Matrix.reindex e e (cmp1 X.B.I.cm.sig X.B.I.J θ (x : HAp X p)) * (Q : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p))

theorem isUnit_det_split_form (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p) :
    IsUnit (jm1 X.B.I.J θ).det := by
  have h := (unit_JR X p).map (th1 X p θ)
  rw [RingHom.map_det] at h
  exact h

theorem stFrameB_of (u : D.what₂.Word) (p : TypX X) (h : StAdaptB X u p) : StFrameB X u p := by
  obtain ⟨θ, hθ, e, Q, l, hl, hy1, hy2, K, hK, ψ, hψ, hker, hred⟩ := h
  refine ⟨K, hK, ψ, hψ, hker, 1, fun x => ?_⟩
  let g1 : GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p) :=
    Q * glRed (algebraMap (Op X p) (FpX X p)) (ψ x) * Q⁻¹
  have hg1 : (g1 : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) =
      Matrix.reindex e e (cmp1 X.B.I.cm.sig X.B.I.J θ (x : HAp X p)) := by
    simp only [g1, Units.val_mul, hred x, ← mul_assoc, Units.mul_inv, one_mul]
    rw [mul_assoc, Units.mul_inv, mul_one]
  have hinj : Function.Injective (algebraMap (Op X p) (FpX X p)) := Subtype.val_injective
  rw [MassDataIdxStIm.mem_Ssub_iff_sG X.B.I.cm.sig X.B.I.J θ hθ e (isUnit_det_split_form X p θ) (frameOf X u) Q l hl
    hy1 hy2 (x : HAp X p) g1 hg1, inv_one, one_mul, mul_one,
    MassDataIdxStIm.mem_sG_iff_map _ hinj (ψ x)]
  simp only [g1, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]

theorem parabolic_image_of_adapted (u : D.what₂.Word) (p : TypX X) (h : StAdaptB X u p) : ParabolicReductionImage X u p := parabolic_image_of_frame X u p (stFrameB_of X u p h)

end Loc

end MassDataIdxSteps
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ParabolicImageOfAdapted =====

-- ===== clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ParabolicImageOfBasisAdapted =====
-- clump-header: {"m": "Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ParabolicImageOfBasisAdapted", "h": "module\n\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ParabolicImageOfAdapted\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxRed MassDataIdxSpl Matrix

section Loc

variable {D : D7} (X : HidaSetting D)

def reindex₂ (p : TypX X) (Q : GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) : GL (Fin X.B.I.n) (FpX X p) :=
  Units.map (Matrix.reindexAlgEquiv (FpX X p) (FpX X p) (idxEquiv X).symm).toMonoidHom Q

def StLatGLx (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)
    (Q : GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) : Prop :=
  ∀ K : Subgroup (HAp X p), (K : Set (HAp X p)) = KvX X p →
    ∃ ψ : K →* GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p), Function.Surjective ψ ∧
      (∀ x : K, (∀ i j, ((ψ x : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p))
        - 1) i j ∈ Ideal.span {((gOf p : ℕ) : Op X p)}) ↔ (x : HAp X p) ∈ KgX X p) ∧
      ∀ x : K, ((glRed (algebraMap (Op X p) (FpX X p)) (ψ x) : GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) :
          Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) =
        ((Q⁻¹ : GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) :
          Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) *
          Matrix.reindex (idxEquiv X) (idxEquiv X) (cmp1 X.B.I.cm.sig X.B.I.J θ (x : HAp X p)) *
          (Q : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p))

end Loc

def LatCoreX : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p),
    IsSplitEquiv X p θ → ∀ Q, LatBasis X p θ (reindex₂ X p Q) → StLatGLx X p θ Q

section Loc2

variable {D : D7} (X : HidaSetting D)

def StAdaptQ (u : D.what₂.Word) (p : TypX X) : Prop :=
  ∃ θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p, IsSplitEquiv X p θ ∧
    ∃ (Q : GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) (l : Fin (D.R.rS + 1) → FpX X p), (∀ b, l b ≠ 0) ∧
      (∀ b, ((Q⁻¹ : GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) :
          Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) *ᵥ
        (pr1 θ (ratV (F := X.B.I.F) (FpX X p) (F0 (frameOf X u) b)) ∘ (idxEquiv X).symm) = Pi.single (pe b) 1) ∧
      (∀ b, (Q : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p))ᵀ *ᵥ
        ((Matrix.reindex (idxEquiv X) (idxEquiv X) (jm1 X.B.I.J θ))ᵀ *ᵥ
          (pr2 θ (ratV (F := X.B.I.F) (FpX X p) (F0 (frameOf X u) b)) ∘ (idxEquiv X).symm)) =
        l b • Pi.single (pf b) 1) ∧
      LatBasis X p θ (reindex₂ X p Q)

theorem stAdaptB_of (hC : LatCoreX) (u : D.what₂.Word) (p : TypX X) (h : StAdaptQ X u p) : StAdaptB X u p := by
  obtain ⟨θ, hθ, Q, l, hl, h1, h2, hL⟩ := h
  have hG := hC X p θ hθ Q hL
  let K : Subgroup (HAp X p) :=
    { carrier := KvX X p
      mul_mem' := by
        intro a b ha hb
        simp only [KvX, Formalism.L2.SG.TypedSets.Kv, Set.mem_setOf_eq] at ha hb ⊢
        exact Subgroup.mul_mem _ ha hb
      one_mem' := by
        simp only [KvX, Formalism.L2.SG.TypedSets.Kv, Set.mem_setOf_eq]
        exact Subgroup.one_mem _
      inv_mem' := by
        intro a ha
        simp only [KvX, Formalism.L2.SG.TypedSets.Kv, Set.mem_setOf_eq] at ha ⊢
        exact Subgroup.inv_mem _ ha }
  obtain ⟨ψ, hψs, hψ1, hψ2⟩ := hG K rfl
  exact ⟨θ, hθ, idxEquiv X, Q, l, hl, h1, h2, K, rfl, ψ, hψs, hψ1, hψ2⟩

theorem parabolic_image_of_basis_adapted (hC : LatCoreX) (u : D.what₂.Word) (p : TypX X) (h : StAdaptQ X u p) :
    ParabolicReductionImage X u p :=
  parabolic_image_of_adapted X u p (stAdaptB_of X hC u p h)

end Loc2

end MassDataIdxSteps
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ParabolicImageOfBasisAdapted =====
