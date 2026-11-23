module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0204
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0225
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0143
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0222
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0123
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaIsotropicStabilizerInertPlace
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0207
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0376

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsJointlySmoothBiThetaWeilRepSecondVariable
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BiActRight

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger GlobalTheory.ChiGrid GlobalTheory.BiTransfer

variable {D : D7}

theorem conjSource_conjAdjoint_apply {S A' : HSp D} (omb : Om S A') (g : GA D S) (h : GA D A') (f : WO S A' → ℂ)
    (y : WO A' S) :
    conjSource (conjAdjoint omb) (negGA A' h, g) (fun y' => f (dagger A' S y')) y = omb (g, h) f (dagger A' S y) := by
  have e1 : conjSource (conjAdjoint omb) (negGA A' h, g) =
      cjEnd (Equiv.refl (WO A' S)) (cjEnd (daggerEquiv S A') (omb (g, h))) := by
    simp only [conjSource, conjAdjoint, MonoidHom.comp_apply, MonoidHom.prodMap, MonoidHom.coe_mk, OneHom.coe_mk,
      MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply, MonoidHom.id_apply, Prod.map]
    rfl
  have e2 : (fun y' => f (dagger A' S y')) =
      GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (Equiv.refl (WO A' S)) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (daggerEquiv S A') f) := by
    funext y'; simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, daggerEquiv]
  rw [e1, e2, cjEnd_cj, cjEnd_cj]
  simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, daggerEquiv]

theorem resS_symm_swap {W A B : HSp D} (d : OrthDec W A B) (T : HSp D) (u : WO A T) (y : WO B T) :
    (d.symm.resS T).symm (y, u) = (d.resS T).symm (u, y) :=
  add_comm (y ⬝ d.pB) (u ⬝ d.pA)

theorem isBiTheta_act_right : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (χS' χA' : (AE D)ˣ →* Circle) (omb : Om S A'), IsWeilDatumO ψ S A' χS' χA' omb → ∀ C, IsBiTheta ψ A S A' C → ∀ q, IsBiTheta ψ A S A' fun u v => omb q (C u) v := by
  intro D ψ A S A' χS' χA' omb hω C hC q
  obtain ⟨g, h⟩ := q
  have hw1 := ((_root_.GlobalTheory.WeilConjAdjoint.conjAdjoint_holds D ψ hω.std S A').conj_adjoint χS' χA' omb hω).1
  have hw2 := ((_root_.GlobalTheory.WeilConjAdjoint.conjAdjoint_holds D ψ hω.std A' S).conj_source χA' χS' (conjAdjoint omb) hw1).1
  let d := sumDec A (negSp A')
  have hG := (GlobalTheory.T.weil_operator_commutes_superposition_slices_source D ψ _ (negSp A') A S d.symm _ _ (conjSource (conjAdjoint omb)) hw2 _ (isThetaFunO_join d hC)
    Unit 0 (fun _ => 0) (fun _ => 0) measurable_const (integrable_zero _ _ _) (negGA A' h, g)).1
  refine isBiTheta_of_join d ?_
  convert hG using 1
  funext x
  have hs : d.symm.resS S x = ((d.resS S x).2, (d.resS S x).1) := by
    apply (d.symm.resS S).symm.injective
    calc
      _ = x := (d.symm.resS S).symm_apply_apply x
      _ = (d.resS S).symm (d.resS S x) := ((d.resS S).symm_apply_apply x).symm
      _ = _ := (resS_symm_swap d S _ _).symm
  simpa [join, hs, resS_symm_swap] using
    (conjSource_conjAdjoint_apply omb g h (C (d.resS S x).1) (d.resS S x).2).symm

end GlobalTheory.BiActRight

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatHalfSourceBoxLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.ExtZero.SBBox

variable {D : D7}

theorem half_add {m n : ℕ} {e : AE D} {u t : Mx D m n} (hu : IsHalf e u) (ht : IsHalf e t) : IsHalf e (u + t) := by
  intro i j
  rw [Matrix.add_apply, mul_add, hu, ht]

theorem half_sub {m n : ℕ} {e : AE D} {u t : Mx D m n} (hu : IsHalf e u) (ht : IsHalf e t) : IsHalf e (u - t) := by
  intro i j
  rw [Matrix.sub_apply, mul_sub, hu, ht]

theorem half_nsmul {m n : ℕ} {e : AE D} {u : Mx D m n} (hu : IsHalf e u) (N : ℕ) : IsHalf e (N • u) := by
  induction N with
  | zero => intro i j; rw [zero_smul, Matrix.zero_apply, mul_zero]
  | succ N ih => rw [succ_nsmul]; exact half_add ih hu

theorem half_mul {m n l : ℕ} {e : AE D} {u : Mx D m n} (hu : IsHalf e u) (x : Mx D n l) :
    IsHalf e (u * x : Mx D m l) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by rw [← mul_assoc, hu]

theorem half_of_res {S A L T : HSp D} (o : OrthDec S A L) {e : AE D} {t : WO S T}
    (h1 : IsHalf e (o.resS T t).1) (h2 : IsHalf e (o.resS T t).2) : IsHalf e t := by
  rw [← (o.resS T).symm_apply_apply t]
  exact half_add (half_mul h1 _) (half_mul h2 _)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {p : SplitPt D k} {T L : HSp D} {n : Type} [Fintype n] [DecidableEq n]

theorem zcol_add (β : Frame p T n) (ζ : Fin L.rank → D.host.E) (y y' : WO L T) :
    zcol β ζ (y + y') = zcol β ζ y + zcol β ζ y' := by
  unfold zcol
  rw [← Matrix.mulVec_add]
  congr 1
  funext i
  rw [Matrix.add_mulVec, Pi.add_apply, map_add (f := _)]; rfl

theorem zcol_zero (β : Frame p T n) (ζ : Fin L.rank → D.host.E) : zcol β ζ 0 = 0 := by
  have := zcol_add β ζ 0 0
  rw [add_zero] at this
  exact left_eq_add.1 this

theorem zcol_nsmul (β : Frame p T n) (ζ : Fin L.rank → D.host.E) (y : WO L T) (N : ℕ) :
    zcol β ζ (N • y) = N • zcol β ζ y := by
  induction N with
  | zero => rw [zero_smul, zero_smul, zcol_zero]
  | succ N ih => rw [succ_nsmul, succ_nsmul, zcol_add, ih]

theorem colFun_ne_zero (β : Frame p T n) (ζ : Fin L.rank → D.host.E) (Λ : Submodule 𝒪[k] (n → k)) (y : WO L T) :
    colFun β ζ (vecInd Λ) y ≠ 0 ↔ IsHalf p.e y ∧ zcol β ζ y ∈ Λ := by
  unfold colFun vecInd
  by_cases h : IsHalf p.e y <;> by_cases h' : zcol β ζ y ∈ Λ <;> simp [h, h']

theorem colFun_add (β : Frame p T n) (ζ : Fin L.rank → D.host.E) (Λ : Submodule 𝒪[k] (n → k)) (y u : WO L T)
    (hu : IsHalf p.e u) (hu' : zcol β ζ u ∈ Λ) :
    colFun β ζ (vecInd Λ) (y + u) = colFun β ζ (vecInd Λ) y := by
  have h1 : IsHalf p.e (y + u) ↔ IsHalf p.e y :=
    ⟨fun h => by simpa using half_sub h hu, fun h => half_add h hu⟩
  have h2 : zcol β ζ (y + u) ∈ Λ ↔ zcol β ζ y ∈ Λ := by
    rw [zcol_add]; exact Λ.add_mem_iff_left hu'
  unfold colFun vecInd
  rw [propext h1, propext h2]

theorem halfInd_ne_zero {m l : ℕ} (e : AE D) (Λ : AddSubgroup (Mx D m l)) (t : Mx D m l) :
    halfInd e Λ t ≠ 0 ↔ t ∈ Λ ∧ IsHalf e t := by
  unfold halfInd
  by_cases h : t ∈ Λ ∧ IsHalf e t <;> simp [h]

theorem isSBHalf_boxS_gen {S A : HSp D} (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (β : Frame p T n)
    (ΛA : AddSubgroup (WO A T)) (ΛS : AddSubgroup (WO S T)) (ΛT : Submodule 𝒪[k] (n → k))
    (hf : halfInd p.e ΛS = o.boxS T (halfInd p.e ΛA) (colFun β ζ (vecInd ΛT)))
    (Φ : WO A T → ℂ) (hΦ : IsSBHalf p.e ΛA Φ) :
    IsSBHalf p.e ΛS (o.boxS T Φ (colFun β ζ (vecInd ΛT))) := by
  have key : ∀ u : WO S T, (u ∈ ΛS ∧ IsHalf p.e u) ↔
      (((o.resS T u).1 ∈ ΛA ∧ IsHalf p.e (o.resS T u).1) ∧
        (IsHalf p.e (o.resS T u).2 ∧ zcol β ζ (o.resS T u).2 ∈ ΛT)) := by
    intro u
    rw [← halfInd_ne_zero, ← halfInd_ne_zero, ← colFun_ne_zero, hf, ← mul_ne_zero_iff]
    rfl
  obtain ⟨hs, N, hN, hinv, hsup⟩ := hΦ
  have hne : ∀ t, o.boxS T Φ (colFun β ζ (vecInd ΛT)) t ≠ 0 →
      Φ (o.resS T t).1 ≠ 0 ∧ IsHalf p.e (o.resS T t).2 ∧ zcol β ζ (o.resS T t).2 ∈ ΛT := by
    intro t ht
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 ht
    exact ⟨h1, (colFun_ne_zero β ζ ΛT _).1 h2⟩
  refine ⟨fun t ht => half_of_res o (hs _ (hne t ht).1) (hne t ht).2.1, N, hN, fun u hu hu' t => ?_, fun t ht => ?_⟩
  · obtain ⟨⟨h1, h2⟩, h3, h4⟩ := (key u).1 ⟨hu, hu'⟩
    unfold OrthDec.boxS
    rw [map_add (f := _), map_nsmul, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, hinv _ h1 h2,
      colFun_add β ζ ΛT _ _ (half_nsmul h3 N) (by rw [zcol_nsmul]; exact nsmul_mem h4 N)]
  · obtain ⟨h1, h2, h3⟩ := hne t ht
    refine ((key (N • t)).2 ?_).1
    rw [map_nsmul, Prod.smul_fst, Prod.smul_snd]
    exact ⟨⟨hsup _ h1, half_nsmul (hs _ h1) N⟩, half_nsmul h2 N, by rw [zcol_nsmul]; exact nsmul_mem h3 N⟩

theorem isSBHalf_boxS : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (S A L T : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (β : Frame p T n) (LA : Lat A) (LS : Lat S) (LT : Lat T) (ΛT : Submodule 𝒪[k] (n → k)), halfInd p.e (latO S T (LS : Set _) (LT : Set _) (· = p.v)) = o.boxS T (halfInd p.e (latO A T (LA : Set _) (LT : Set _) (· = p.v))) (GlobalTheory.FinPl.ExtZero.colFun β ζ (vecInd ΛT)) → ∀ Φ, IsSBHalf p.e (latO A T (LA : Set _) (LT : Set _) (· = p.v)) Φ → IsSBHalf p.e (latO S T (LS : Set _) (LT : Set _) (· = p.v)) (o.boxS T Φ (GlobalTheory.FinPl.ExtZero.colFun β ζ (vecInd ΛT))) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ o ζ β _ _ _ ΛT hf Φ hΦ => isSBHalf_boxS_gen o ζ β _ _ ΛT hf Φ hΦ

end GlobalTheory.FinPl.ExtZero.SBBox

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatHalfTargetBoxDualIndicator
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.ExtZero

namespace RowSB

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {p : SplitPt D k} {n : Type} [Fintype n] [DecidableEq n]

theorem isHalf_add_of {e : AE D} {a b : ℕ} {x y : Mx D a b} (hx : IsHalf e x) (hy : IsHalf e y) :
    IsHalf e (x + y) := by
  intro i j
  simp only [Matrix.add_apply, mul_add, hx i j, hy i j]

theorem isHalf_nsmul_of {e : AE D} {a b : ℕ} {x : Mx D a b} (hx : IsHalf e x) (m : ℕ) : IsHalf e (m • x) := by
  intro i j
  rw [show (m • x) i j = m • x i j from rfl, nsmul_eq_mul, mul_left_comm, hx i j]

theorem isHalf_of_add {e : AE D} {a b : ℕ} {x y : Mx D a b} (hxy : IsHalf e (x + y)) (hy : IsHalf e y) :
    IsHalf e x := by
  intro i j
  have h := hxy i j
  rw [Matrix.add_apply, mul_add, hy i j] at h
  exact add_right_cancel h

theorem isHalf_resT_symm_pair {S A L : HSp D} (o : OrthDec S A L) (T : HSp D) {e : AE D} {a : WO T A} {b : WO T L}
    (ha : IsHalf e a) (hb : IsHalf e b) : IsHalf e ((o.resT T).symm (a, b)) := by
  intro i j
  rw [OrthDec.resT_symm_apply]
  simp only [Matrix.add_apply, Matrix.mul_apply, mul_add, Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun x _ => by rw [mul_left_comm, ha]
  · exact Finset.sum_congr rfl fun x _ => by rw [mul_left_comm, hb]

theorem zrow_add' {T L : HSp D} (β : Frame p T n) (ζ : Fin L.rank → D.host.E) (x y : WO T L) :
    zrow β ζ (x + y) = zrow β ζ x + zrow β ζ y := by
  simp only [zrow, Matrix.vecMul_add, Pi.add_apply, map_add (f := _)]
  rw [← smul_add, ← Matrix.add_vecMul]
  rfl

def zrowHom {T L : HSp D} (β : Frame p T n) (ζ : Fin L.rank → D.host.E) : WO T L →+ (n → k) :=
  AddMonoidHom.mk' (zrow β ζ) (zrow_add' β ζ)

theorem zrow_nsmul' {T L : HSp D} (β : Frame p T n) (ζ : Fin L.rank → D.host.E) (m : ℕ) (x : WO T L) :
    zrow β ζ (m • x) = m • zrow β ζ x :=
  map_nsmul (zrowHom β ζ) m x

theorem inDual_add' {Λ : Submodule 𝒪[k] (n → k)} {η ξ : n → k} (h : InDual Λ η) (h' : InDual Λ ξ) :
    InDual Λ (η + ξ) := fun y hy => by
  rw [add_dotProduct]; exact add_mem (h y hy) (h' y hy)

theorem inDual_sub' {Λ : Submodule 𝒪[k] (n → k)} {η ξ : n → k} (h : InDual Λ η) (h' : InDual Λ ξ) :
    InDual Λ (η - ξ) := fun y hy => by
  rw [sub_dotProduct]; exact sub_mem (h y hy) (h' y hy)

theorem inDual_nsmul' {Λ : Submodule 𝒪[k] (n → k)} {η : n → k} (h : InDual Λ η) (m : ℕ) :
    InDual Λ (m • η) := fun y hy => by
  rw [smul_dotProduct]; exact nsmul_mem (h y hy) m

theorem rowFun_dualInd_ne_zero {T L : HSp D} (β : Frame p T n) (ζ : Fin L.rank → D.host.E)
    (ΛT : Submodule 𝒪[k] (n → k)) {y : WO T L} (h : rowFun β ζ (dualInd ΛT) y ≠ 0) :
    IsHalf p.e y ∧ InDual ΛT (zrow β ζ y) := by
  unfold rowFun dualInd at h
  by_cases hy : IsHalf p.e y
  · rw [if_pos hy] at h
    by_cases hd : InDual ΛT (zrow β ζ y)
    · exact ⟨hy, hd⟩
    · rw [if_neg hd] at h; exact absurd rfl h
  · rw [if_neg hy] at h; exact absurd rfl h

theorem rowFun_dualInd_eq_one {T L : HSp D} (β : Frame p T n) (ζ : Fin L.rank → D.host.E)
    (ΛT : Submodule 𝒪[k] (n → k)) {y : WO T L} (hy : IsHalf p.e y) (hd : InDual ΛT (zrow β ζ y)) :
    rowFun β ζ (dualInd ΛT) y = 1 := by
  unfold rowFun dualInd
  rw [if_pos hy, if_pos hd]

theorem rowFun_dualInd_add_nsmul {T L : HSp D} (β : Frame p T n) (ζ : Fin L.rank → D.host.E)
    (ΛT : Submodule 𝒪[k] (n → k)) {y : WO T L} (hy : IsHalf p.e y) (hd : InDual ΛT (zrow β ζ y)) (m : ℕ)
    (x : WO T L) : rowFun β ζ (dualInd ΛT) (x + m • y) = rowFun β ζ (dualInd ΛT) x := by
  have hz : zrow β ζ (x + m • y) = zrow β ζ x + m • zrow β ζ y := by
    rw [zrow_add', zrow_nsmul']
  have hm := inDual_nsmul' hd m
  unfold rowFun dualInd
  by_cases hx : IsHalf p.e x
  · rw [if_pos (isHalf_add_of hx (isHalf_nsmul_of hy m)), if_pos hx, hz]
    have hiff : InDual ΛT (zrow β ζ x + m • zrow β ζ y) ↔ InDual ΛT (zrow β ζ x) :=
      ⟨fun h => by simpa using inDual_sub' h hm, fun h => inDual_add' h hm⟩
    by_cases hd' : InDual ΛT (zrow β ζ x)
    · rw [if_pos hd', if_pos (hiff.2 hd')]
    · rw [if_neg hd', if_neg (fun h => hd' (hiff.1 h))]
  · rw [if_neg hx, if_neg (fun h => hx (isHalf_of_add h (isHalf_nsmul_of hy m)))]

theorem halfInd_eq_one_iff' {e : AE D} {a b : ℕ} (Λ : AddSubgroup (Mx D a b)) (t : Mx D a b) :
    halfInd e Λ t = 1 ↔ t ∈ Λ ∧ IsHalf e t := by
  unfold halfInd
  split_ifs with h <;> simp [h]

theorem halfInd_ne_zero_iff' {e : AE D} {a b : ℕ} (Λ : AddSubgroup (Mx D a b)) (t : Mx D a b) :
    halfInd e Λ t ≠ 0 ↔ t ∈ Λ ∧ IsHalf e t := by
  unfold halfInd
  split_ifs with h <;> simp [h]

end RowSB

open RowSB

theorem isSBHalf_boxT_rowFun_dualInd : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (S A L T : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (β : Frame p T n) (LA : Lat A) (LS : Lat S) (LT : Lat T) (ΛT : Submodule 𝒪[k] (n → k)), halfInd p.e (latO T S (LT : Set _) (LS : Set _) (· = p.v)) = o.boxT T (halfInd p.e (latO T A (LT : Set _) (LA : Set _) (· = p.v))) (GlobalTheory.FinPl.ExtZero.rowFun β ζ (dualInd ΛT)) → ∀ Φ, IsSBHalf p.e (latO T A (LT : Set _) (LA : Set _) (· = p.v)) Φ → IsSBHalf p.e (latO T S (LT : Set _) (LS : Set _) (· = p.v)) (o.boxT T Φ (GlobalTheory.FinPl.ExtZero.rowFun β ζ (dualInd ΛT))) := by
  intro D k _ _ _ _ p n _ _ S A L T o ζ β LA LS LT ΛT H Φ hΦ
  obtain ⟨hsupp, m, hm, hinv, hlat⟩ := hΦ
  have hH : ∀ w, halfInd p.e (latO T S (LT : Set _) (LS : Set _) (· = p.v)) w =
      halfInd p.e (latO T A (LT : Set _) (LA : Set _) (· = p.v)) (o.resT T w).1 *
        rowFun β ζ (dualInd ΛT) (o.resT T w).2 := fun w => congrFun H w
  have hbox : ∀ w, o.boxT T Φ (rowFun β ζ (dualInd ΛT)) w =
      Φ (o.resT T w).1 * rowFun β ζ (dualInd ΛT) (o.resT T w).2 := fun w => rfl
  refine ⟨fun t ht => ?_, m, hm, fun u hu hhu t => ?_, fun t ht => ?_⟩
  · rw [hbox] at ht
    have h1 := hsupp _ (left_ne_zero_of_mul ht)
    have h2 := (rowFun_dualInd_ne_zero β ζ ΛT (right_ne_zero_of_mul ht)).1
    have := isHalf_resT_symm_pair o T h1 h2
    rwa [Prod.mk.eta, AddEquiv.symm_apply_apply] at this
  · have hu1 : halfInd p.e (latO T S (LT : Set _) (LS : Set _) (· = p.v)) u = 1 :=
      (halfInd_eq_one_iff' _ _).2 ⟨hu, hhu⟩
    rw [hH] at hu1
    have hA := (halfInd_ne_zero_iff' _ _).1 (left_ne_zero_of_mul_eq_one hu1)
    have hR := rowFun_dualInd_ne_zero β ζ ΛT (right_ne_zero_of_mul_eq_one hu1)
    rw [hbox, hbox, map_add (f := _), map_nsmul, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      hinv _ hA.1 hA.2, rowFun_dualInd_add_nsmul β ζ ΛT hR.1 hR.2]
  · rw [hbox] at ht
    have hΦt := left_ne_zero_of_mul ht
    have h1 := hsupp _ hΦt
    have hR := rowFun_dualInd_ne_zero β ζ ΛT (right_ne_zero_of_mul ht)
    have hmt : halfInd p.e (latO T S (LT : Set _) (LS : Set _) (· = p.v)) (m • t) = 1 := by
      rw [hH, map_nsmul, Prod.smul_fst, Prod.smul_snd,
        (halfInd_eq_one_iff' _ _).2 ⟨hlat _ hΦt, isHalf_nsmul_of h1 m⟩,
        rowFun_dualInd_eq_one β ζ ΛT (isHalf_nsmul_of hR.1 m) (by rw [zrow_nsmul']; exact inDual_nsmul' hR.2 m),
        one_mul]
    exact ((halfInd_eq_one_iff' _ _).1 hmt).1

end GlobalTheory.FinPl.ExtZero

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaFunOSourceSlice
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MixModel.OrthDec

theorem isThetaFunO_slice : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S A L T : HSp D) (o : OrthDec S A L)
    (f : WO S T → ℂ) (y : WO L T), IsThetaFunO ψ S T f →
      IsThetaFunO ψ A T (fun w => f ((o.resS T).symm (w, y))) :=
  fun _ _ _ _ _ _ o _ y hf => GlobalTheory.BoxSlice.isThetaFunO_slice_left o hf y

end GlobalTheory.MixModel.OrthDec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaIsotropicStabilizerInertPlaceStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_isotropicStabilizer_inertPlace : ∀ (D : D7) (T T₀ : HSp D) (r : ℕ) (d : HypDec T T₀ r) (v : FinPl D), ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v → ∀ y : Gv T v, ∃ q k : Gv T v, emb D.sp.cm.sig T.gram v q ∈ stab d ∧ k ∈ stabLoc D.sp.cm.sig T.gram (frameLat T) v ∧ y = q * k := by
  first | exact @GlobalTheory.InertIwasawaIso.iwasawa_inert | exact GlobalTheory.InertIwasawaIso.iwasawa_inert | (intros; apply GlobalTheory.InertIwasawaIso.iwasawa_inert <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MeasurableSetTwistPlaceChainStepDatumMatrixSuppoStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl IsBase onHalf phiQ rdQ)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurableSet_twistPlaceChainStepDatumMatrixSupport : ∀ (D : D7) (v : FinPl D) (a b r : ℕ), MeasurableSet (GlobalTheory.NrmVol.suppQ (a := a) (b := b) v r) := by
  first | exact @GlobalTheory.NrmVol.measurableSet_suppQ | exact GlobalTheory.NrmVol.measurableSet_suppQ | (intros; apply GlobalTheory.NrmVol.measurableSet_suppQ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinateOriginUnipotentRadicalInvariant
section
namespace I195MixedCoordinates_069c5864e5661f762e792771

open Formalism.BasicNotions Formalism.BasicNotions.TH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

public noncomputable abbrev source
    {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) : WO S₀ T → ℂ :=
  fun w₀ => ∫ a in 𝓕, heisO ψ S T (a * d.pY)
    (heisO ψ S T (x * d.pX) (heisO ψ S T (w₀ * d.p0) f)) 0 ∂μ

end I195MixedCoordinates_069c5864e5661f762e792771

public noncomputable abbrev _root_.I195MixedCoordinates_46859e632a5b1b7714de2075.source :=
  @_root_.I195MixedCoordinates_069c5864e5661f762e792771.source

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.UnipZero

theorem heisO_zero {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f : WO S T → ℂ) : heisO ψ S T 0 f = f := by
  funext w
  have h : symplOH S T w 0 = 0 := by
    first | exact symplOH_zero_right .. | simp [symplOH] | (rw [symplOH]; simp)
  simp [heisO, h]

theorem mixS_zero_unip : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), IsCovolOne (ratMx D T.rank ρ) μ 𝓕 → ∀ f, IsThetaFunO ψ S T f → (∀ b, (_root_.I195MixedCoordinates_069c5864e5661f762e792771.source d) T ψ μ 𝓕 (om (d.nB b, 1) f) 0 = (_root_.I195MixedCoordinates_069c5864e5661f762e792771.source d) T ψ μ 𝓕 (f) 0) ∧ ∀ c, (_root_.I195MixedCoordinates_069c5864e5661f762e792771.source d) T ψ μ 𝓕 (om (d.nC c, 1) f) 0 = (_root_.I195MixedCoordinates_069c5864e5661f762e792771.source d) T ψ μ 𝓕 (f) 0 := by
  intro D ψ S S₀ T ρ d χS χT om hW μ 𝓕 hμ f hf
  rcases Nat.eq_zero_or_pos ρ with hρ | hρ
  · subst hρ
    obtain ⟨-, -, h0⟩ := _root_.GlobalTheory.Unf.mixRankZero D ψ
    obtain ⟨-, hB, hC⟩ := h0 S S₀ d
    refine ⟨fun b => ?_, fun c => ?_⟩
    · rw [hB b, show ((1 : GA D S), (1 : GA D T)) = 1 from rfl, map_one]; rfl
    · rw [hC c, show ((1 : GA D S), (1 : GA D T)) = 1 from rfl, map_one]; rfl
  · obtain ⟨hiso, hrat, -, -, -, hres, -, hnB, hnC⟩ := _root_.GlobalTheory.Bridge.heis_bridge D ψ S S₀ T ρ d
    have hμ' : IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D T.rank ρ) μ 𝓕 := by rw [hrat]; exact hμ
    have key : ∀ n : NI S d.e, (_root_.I195MixedCoordinates_069c5864e5661f762e792771.source d) T ψ μ 𝓕 (om ((n : GA D S), 1) f) 0 = (_root_.I195MixedCoordinates_069c5864e5661f762e792771.source d) T ψ μ 𝓕 f 0 := by
      intro n
      change I195MixedCoordinates_61fbc522a99e851221ffe16d.source d T ψ μ 𝓕 (om ((n : GA D S), 1) f) 0 = I195MixedCoordinates_61fbc522a99e851221ffe16d.source d T ψ μ 𝓕 f 0
      rw [hres, hres, map_zero, heisO_zero, heisO_zero]
      exact _root_.GlobalTheory.UnipRes.res_unip D S S₀ T ρ d.e d.i₀ (hiso hρ) ψ χS χT om hW μ 𝓕 hμ' n f hf
    exact ⟨fun b => key ⟨_, hnB b⟩, fun c => key ⟨_, hnC c⟩⟩

end GlobalTheory.UnipZero
end
end

