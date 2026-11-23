module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1883
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.MemRangeOfIsAlgebraicRatFun
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0219
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelOfSplitAndLevelCoeffExist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1821
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTransporterMovesFrameReadsInverse
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1878
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1535
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0519
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0335
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DeterminantSectionRule
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.PremisesOfProper
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0495
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0006
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalisedModelUniformisationBaseChange
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0040

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelChangeMap
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.FlatModel

namespace GlobalTheory.LevelMapBase

theorem levelMap_coeff_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (hle : c.F ≤ c'.F),
    1 ≤ Dw.p + Dw.q → l.Dvd l' →
    ∃ (r : Xo'.XF c' ⟶ Xo.XF c)
      (h : r ≫ pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) =
        pullback.snd Xo'.s (spMap (IntermediateField.inclusion c'.le).toRingHom) ≫ spMap (IntermediateField.inclusion hle).toRingHom)
      (r₀ : Xo'.X ⟶ Xo.X) (_ : SABMap Xo'.univ.t Xo.univ.t r₀),
      r ≫ pullback.fst _ _ = pullback.fst _ _ ≫ r₀ ∧ IsFinite (pullback.lift r _ h) ∧ Etale (pullback.lift r _ h) ∧
        Surjective (pullback.lift r _ h) := by
  intro E _ _ _ H Dw l l' Xo Xo' c c' hle hpq hd
  obtain ⟨r₀, jK, m, hk, -, -, -, -, hc⟩ := (_root_.GlobalTheory.moduliScheme_levelMaps_heckePoints.2 E H Dw hpq).1 l l' Xo Xo' hd
  have hle₁ : KA l ≤ c'.F := fun x hx => by
    have := c'.le (jK ⟨x, hx⟩).2
    rwa [hk] at this
  let c₁ : Coeff l :=
    { F := c'.F
      fin := c'.fin
      conj := c'.conj
      zeta_mem := by
        obtain ⟨e, he⟩ := GlobalTheory.LevelExist.zeta_eq_pow_of_dvd (a := l.M') (GlobalTheory.LevelExist.M'_pos l')
          (Nat.lcm_dvd (hd.1.trans (Nat.dvd_lcm_left _ _)) (hd.2.2.trans (Nat.dvd_lcm_right _ _)) : l.M' ∣ l'.M')
        rw [he]
        exact pow_mem c'.zeta_mem e
      le := hle₁ }
  obtain ⟨rF, e1, e2, f1, f2, f3, -⟩ := hc c₁ c' rfl
  have hid : spMap (IntermediateField.inclusion (le_refl c'.F)).toRingHom = 𝟙 (Sp c'.F) := by
    rw [← Spec.map_id]
    rfl
  have e2' : rF ≫ pullback.snd _ _ = pullback.snd _ _ := e2.trans ((congrArg _ hid).trans (Category.comp_id _))
  have hi : spMap (IntermediateField.inclusion hle).toRingHom ≫ spMap (IntermediateField.inclusion c.le).toRingHom =
      spMap (IntermediateField.inclusion c₁.le).toRingHom := by
    rw [← Spec.map_comp]
    rfl
  let b : Xo.XF c₁ ⟶ Xo.XF c :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ spMap (IntermediateField.inclusion hle).toRingHom)
      (by rw [Category.assoc, hi, pullback.condition])
  have hb1 : b ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _
  have hb2 : b ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (IntermediateField.inclusion hle).toRingHom :=
    pullback.lift_snd _ _ _
  have hp : IsPullback b (pullback.snd _ _) (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
      (spMap (IntermediateField.inclusion hle).toRingHom) := by
    refine IsPullback.of_right ?_ hb2 (IsPullback.of_hasPullback _ _)
    rw [hb1, hi]
    exact IsPullback.of_hasPullback _ _
  have h : (rF ≫ b) ≫ pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) =
      pullback.snd Xo'.s (spMap (IntermediateField.inclusion c'.le).toRingHom) ≫
        spMap (IntermediateField.inclusion hle).toRingHom := by
    rw [Category.assoc, hb2, reassoc_of% e2']
  have hlift : pullback.lift (rF ≫ b) _ h = rF ≫ hp.isoPullback.hom := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, IsPullback.isoPullback_hom_fst]
    · rw [pullback.lift_snd, Category.assoc, IsPullback.isoPullback_hom_snd, e2']
  refine ⟨rF ≫ b, h, r₀, m, ?_, ?_, ?_, ?_⟩
  · rw [Category.assoc, hb1, e1]
  · rw [hlift]; infer_instance
  · rw [hlift]; infer_instance
  · rw [hlift]; infer_instance

end GlobalTheory.LevelMapBase
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelChangeTransportersAllComponents
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn

namespace GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_transp_all : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)), ∃ ψ : ∀ k : (uAt r v i).Comp, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] latQ p r i v k, ∀ (γ : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l) (k : (uAt r v i).Comp), ∃ (k' : (uAt r v i).Comp) (a : GL (Fin D.R.r) D.host.E), IsTransp p r i v ψ γ k k' a := by
  intro D L hT Gi Gl Kc Y cX ex Csz p hp r h hr i v
  obtain ⟨ψ, h1⟩ := _root_.GlobalTheory.ShareOn.exists_movesAt_readsInv p hp r h hr i v
  refine ⟨ψ, fun γ k => ?_⟩
  let V := Frame ((uAt r v i).X k).Ψ D.R.r
  let Dk : Set V := ((uAt r v i).X k).dom
  have hDo : IsOpen Dk := FourierCoefficientDomain.isOpen_dom _
  have hDn : Dk.Nonempty := (GlobalTheory.frames_isConnected D.host.E D.R.r ((uAt r v i).X k)).nonempty
  let ι := Σ k' : (uAt r v i).Comp, {a : GL (Fin D.R.r) D.host.E //
    ∃ hm : GlobalTheory.LevelCusp.IsMatch ((uAt r v i).X k) ((uAt r v i).X k') a, ReadsInv p r i v ψ γ k k' a}
  let S : ι → Set V := fun c => {x | ∃ hx : x ∈ Dk, MovesAt p r i v γ k c.1 c.2.1 c.2.2.1 x hx}
  haveI : Countable ι := inferInstance
  obtain ⟨x₀, hx₀⟩ := hDn
  haveI : Nonempty ι := by
    obtain ⟨k', a, hm, hR, -⟩ := h1 γ k x₀ hx₀
    exact ⟨⟨k', a, hm, hR⟩⟩
  haveI : Nonempty Dk := ⟨⟨x₀, hx₀⟩⟩
  haveI : LocallyCompactSpace Dk := hDo.locallyCompactSpace
  let T : ι → Set Dk := fun c => Subtype.val ⁻¹' closure (S c)
  have hTc : ∀ c, IsClosed (T c) := fun c => isClosed_closure.preimage continuous_subtype_val
  have hTu : ⋃ c, T c = Set.univ := by
    refine Set.eq_univ_of_forall fun y => ?_
    obtain ⟨k', a, hm, hR, hM⟩ := h1 γ k y.1 y.2
    exact Set.mem_iUnion.2 ⟨⟨k', a, hm, hR⟩, subset_closure ⟨y.2, hM⟩⟩
  obtain ⟨c, hc⟩ := nonempty_interior_of_iUnion_of_closed hTc hTu
  obtain ⟨k', a, hm, hR⟩ := c
  refine ⟨k', a, isTransp_of_movesAt hm ?_ hR⟩
  refine _root_.GlobalTheory.ShareOn.movesAt_of_dense p hp r h hr i v γ k k' a hm (Subtype.val '' interior (T ⟨k', a, hm, hR⟩))
    (hDo.isOpenMap_subtype_val _ isOpen_interior) (hc.image _) ?_ ?_
  · rintro _ ⟨y, -, rfl⟩
    exact y.2
  · rintro _ ⟨y, hy, rfl⟩
    have hy' : y ∈ T ⟨k', a, hm, hR⟩ := interior_subset hy
    exact hy'

end GlobalTheory.ShareOn

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieDeterminantLineRatioFunction
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam
  GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

namespace GlobalTheory.DetRatio

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {l : Level H}
  {S X : Scheme.{0}} {c : Coeff l} {t : SAB H S} {π : X ⟶ S} {s : X ⟶ Sp c.F} {V : Set X} {τ : E →+* ℂ}
  {p q : ℕ} {R R' : Type} [CommRing R] [CommRing R'] {σ σ' : Rule t π p q}

theorem sec_pull (hσ : IsSection t π s V (HermitianCompactForm.chi c τ) σ) (g : R →+* R') {j : c.F →+* R} {j' : c.F →+* R'}
    {x : Sp R ⟶ X} {v w} {x' : Sp R' ⟶ X} {v' w'}
    (h : IsFrame t π s V (HermitianCompactForm.chi c τ) j x v w) (h' : IsFrame t π s V (HermitianCompactForm.chi c τ) j' x' v' w')
    (hx : x' = spMap g ≫ x) (a : ∀ i, (v' i).left = spMap (Chart.dualMapR g) ≫ (v i).left)
    (b : ∀ i, (w' i).left = spMap (Chart.dualMapR g) ≫ (w i).left) : σ R' x' v' w' = g (σ R x v w) :=
  hσ.1 R R' g (Chart.dualMapR g) j _ x x' v w v' w'
    (fun a => by ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl])
    (by ext <;> simp [Chart.dualMapR]) h h' hx a b

theorem ratio_frame (hσ : IsSection t π s V (HermitianCompactForm.chi c τ) σ) (hn : NowhereZero t π s V (HermitianCompactForm.chi c τ) σ)
    (hσ' : IsSection t π s V (HermitianCompactForm.chi c τ) σ') {j : c.F →+* R} {x : Sp R ⟶ X} {v w v' w'}
    (h : IsFrame t π s V (HermitianCompactForm.chi c τ) j x v w) (h' : IsFrame t π s V (HermitianCompactForm.chi c τ) j x v' w') {a : R}
    (e : σ' R x v w = a * σ R x v w) : σ' R x v' w' = a * σ R x v' w' := by
  have h₁ : IsFrame t π s V (HermitianCompactForm.chi c τ) j x v' w := ⟨h.1, h.2.1, h'.2.2.1, h.2.2.2⟩
  choose M hM using fun i => (h.2.2.1.2 _ (h'.2.2.1.1 i)).exists
  choose N hN using fun i => (h.2.2.2.2 _ (h'.2.2.2.1 i)).exists
  have ow : ∀ i, IsCombAt (x ≫ π) ((1 : Matrix (Fin q) (Fin q) R) i) w (w i) :=
    fun i => DetExtendZero.comb_one (fun k => (h.2.2.2.1 k).1) i
  have ov : ∀ i, IsCombAt (x ≫ π) ((1 : Matrix (Fin p) (Fin p) R) i) v' (v' i) :=
    fun i => DetExtendZero.comb_one (fun k => (h'.2.2.1.1 k).1) i
  have e1 := hσ.2 R j x v w v' w (Matrix.of M) 1 h h₁ hM ow
  have e1' := hσ'.2 R j x v w v' w (Matrix.of M) 1 h h₁ hM ow
  have e2 := hσ.2 R j x v' w v' w' 1 (Matrix.of N) h₁ h' ov hN
  have e2' := hσ'.2 R j x v' w v' w' 1 (Matrix.of N) h₁ h' ov hN
  rw [Matrix.det_one, _root_.one_mul] at e1 e1' e2 e2'
  have hu : IsUnit (Matrix.of M).det := isUnit_of_mul_isUnit_left (e1 ▸ hn R j x v w h)
  have e3 : σ' R x v' w = a * σ R x v' w := by
    refine hu.mul_left_cancel ?_
    rw [← e1', e, e1]; ring
  rw [← e2', ← e2, e3]; ring

theorem ratio_pull (hσ : IsSection t π s V (HermitianCompactForm.chi c τ) σ) (hn : NowhereZero t π s V (HermitianCompactForm.chi c τ) σ)
    (hσ' : IsSection t π s V (HermitianCompactForm.chi c τ) σ') (g : R →+* R') {j : c.F →+* R} {j' : c.F →+* R'}
    {x : Sp R ⟶ X} {v w} {x' : Sp R' ⟶ X} {v' w'}
    (h : IsFrame t π s V (HermitianCompactForm.chi c τ) j x v w) (h' : IsFrame t π s V (HermitianCompactForm.chi c τ) j' x' v' w')
    (hx : x' = spMap g ≫ x) {a : R} (e : σ' R x v w = a * σ R x v w) :
    σ' R' x' v' w' = g a * σ R' x' v' w' := by
  obtain ⟨v₁, w₁, h₁, a₁, b₁⟩ := exists_pull g h hx
  obtain rfl := (exists_chg g h h' hx).1
  refine ratio_frame hσ hn hσ' h₁ h' ?_
  rw [sec_pull hσ g h h₁ hx a₁ b₁, sec_pull hσ' g h h₁ hx a₁ b₁, e, map_mul]

theorem exists_ratio_affine (hσ : IsSection t π s V (HermitianCompactForm.chi c τ) σ)
    (hn : NowhereZero t π s V (HermitianCompactForm.chi c τ) σ) (hσ' : IsSection t π s V (HermitianCompactForm.chi c τ) σ')
    {W : X.Opens} (hW : IsAffineOpen W) {j₀ : c.F →+* Γ(X, W)} {v₀ w₀}
    (h₀ : IsFrame t π s V (HermitianCompactForm.chi c τ) (p := p) (q := q) j₀ (show Sp Γ(X, W) ⟶ X from hW.fromSpec) v₀ w₀) :
    ∃ f : Γ(X, W), ∀ (R : Type) [CommRing R] (j : c.F →+* R) (x : Sp R ⟶ X) v w, ⊤ ≤ x ⁻¹ᵁ W →
      IsFrame t π s V (HermitianCompactForm.chi c τ) j x v w → σ' R x v w = valR x W f * σ R x v w := by
  obtain ⟨u, hu⟩ := hn _ j₀ _ v₀ w₀ h₀
  refine ⟨σ' _ _ v₀ w₀ * u.inv, fun R _ j x v w hx h => ?_⟩
  rw [Points.valR_eq x W hx]
  refine ratio_pull hσ hn hσ' (Points.valMap x W hx).hom h₀ h (Points.specMap_valMap_fromSpec hW x hx).symm ?_
  rw [← hu, _root_.mul_assoc, u.inv_val, _root_.mul_one]

theorem valR_fromSpec {A : X.Opens} (hA : IsAffineOpen A) (f : Γ(X, A)) :
    valR (show Sp Γ(X, A) ⟶ X from hA.fromSpec) A f = f := by
  have hx : ⊤ ≤ (show Sp Γ(X, A) ⟶ X from hA.fromSpec) ⁻¹ᵁ A := hA.fromSpec_preimage_self.ge
  rw [Points.valR_eq _ A hx]
  have : Points.valMap (show Sp Γ(X, A) ⟶ X from hA.fromSpec) A hx = 𝟙 _ := by
    apply Spec.map_injective
    rw [← cancel_mono hA.fromSpec, Points.specMap_valMap_fromSpec]
    exact ((congrArg (· ≫ hA.fromSpec) (Spec.map_id _)).trans (Category.id_comp _)).symm
  rw [this]
  rfl

end GlobalTheory.DetRatio


open GlobalTheory.DetRatio in
theorem GlobalTheory.detLine_exists_ratio (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (l : Level H) (c : Coeff l) (S X : Scheme.{0}) (t : SAB H S) (π : X ⟶ S) (s : X ⟶ Sp c.F) (τ : E →+* ℂ)
    (p q : ℕ) (V : X.Opens) (σ σ' : Rule t π p q) (hc : FrameCover t π s V (HermitianCompactForm.chi c τ) p q)
    (hσ : IsSection t π s V (HermitianCompactForm.chi c τ) σ) (hn : NowhereZero t π s V (HermitianCompactForm.chi c τ) σ)
    (hσ' : IsSection t π s V (HermitianCompactForm.chi c τ) σ') :
    ∃ f : Γ(X, V), ∀ (R : Type) [CommRing R] (j : c.F →+* R) (x : Sp R ⟶ X) v w,
      IsFrame t π s V (HermitianCompactForm.chi c τ) j x v w → σ' R x v w = valR x V f * σ R x v w := by
  choose W hW j₀ v₀ w₀ hz h₀ using fun z : V => hc z z.2
  choose f hf using fun z : V => exists_ratio_affine hσ hn hσ' (hW z) (h₀ z)
  have hle : ∀ z, W z ≤ V := fun z y hy => (h₀ z).2.1 (by
    change y ∈ Set.range (hW z).fromSpec
    rw [(hW z).range_fromSpec]; exact hy)
  have hcov : V ≤ iSup W := fun y hy => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨y, hy⟩, hz _⟩
  have hcomp : TopCat.Presheaf.IsCompatible X.presheaf W f := by
    intro a b
    refine X.sheaf.eq_of_locally_eq' (fun A : {A : X.affineOpens // A.1 ≤ W a ⊓ W b} => A.1.1) (W a ⊓ W b)
      (fun A => homOfLE A.2) (fun y hy => ?_) _ _ fun A => ?_
    · obtain ⟨_, ⟨A, hA, rfl⟩, hy', hA'⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hy (W a ⊓ W b).2
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨A, hA⟩, hA'⟩, hy'⟩
    · obtain ⟨⟨A, hA⟩, hAle⟩ := A
      replace hA : IsAffineOpen A := hA
      have hx : ⊤ ≤ (show Sp Γ(X, A) ⟶ X from hA.fromSpec) ⁻¹ᵁ A := hA.fromSpec_preimage_self.ge
      have hxa := Points.le_preimage_mono _ (hAle.trans inf_le_left) hx
      have hxb := Points.le_preimage_mono _ (hAle.trans inf_le_right) hx
      have hxab := Points.le_preimage_mono _ hAle hx
      obtain ⟨v, w, h, -, -⟩ := exists_pull (Points.valMap _ (W a) hxa).hom (h₀ a)
        (Points.specMap_valMap_fromSpec (hW a) _ hxa).symm
      have e := (hn _ _ _ v w h).mul_right_cancel ((hf a _ _ _ v w hxa h).symm.trans (hf b _ _ _ v w hxb h))
      refine (valR_fromSpec hA _).symm.trans (Eq.trans ?_ (valR_fromSpec hA _))
      refine (Points.valR_res _ hAle hx _).trans (Eq.trans ?_ (Points.valR_res _ hAle hx _).symm)
      exact (Points.valR_res _ inf_le_left hxab _).trans (e.trans (Points.valR_res _ inf_le_right hxab _).symm)
  obtain ⟨F, hF, -⟩ := X.sheaf.existsUnique_gluing' W V (fun z => homOfLE (hle z)) hcov f hcomp
  refine ⟨F, fun R _ j x v w h => ?_⟩
  have hxV : ⊤ ≤ x ⁻¹ᵁ V := fun y _ => h.2.1 ⟨y, rfl⟩
  rw [← sub_eq_zero]
  refine eq_zero_of_localization _ fun J hJ => ?_
  let g := algebraMap R (Localization.AtPrime J)
  obtain ⟨v₁, w₁, h₁, a₁, b₁⟩ := exists_pull g h rfl
  let z : V := ⟨(spMap g ≫ x) (IsLocalRing.closedPoint (Localization.AtPrime J)), h₁.2.1 ⟨_, rfl⟩⟩
  have hxW : ⊤ ≤ (spMap g ≫ x) ⁻¹ᵁ W z := (Points.le_preimage_iff _ _).2 (hz z)
  have e := hf z _ _ _ v₁ w₁ hxW h₁
  rw [sec_pull hσ g h h₁ rfl a₁ b₁, sec_pull hσ' g h h₁ rfl a₁ b₁, ← hF z] at e
  have e' := (Points.valR_res _ (hle z) hxW F).trans (Points.valR_spMap_comp g x V hxV F)
  change g _ = 0
  rw [map_sub, map_mul, ← e', sub_eq_zero]
  exact e
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieEigenBasisOfIntegralFramedPoint
section
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.BdryUnit
open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace GlobalTheory.IntFrameLift

open ReciprocityTheory.ChartRestriction.G.Semi

theorem exists_eigenBasis_sameVec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (T : CDVR) (io : c.F →+* T.Fr) (φ : c.F →+* T.V), (algebraMap T.V T.Fr).comp φ = io → ∀ (y : letI := io.toAlgebra; FrPt Xo c T.Fr), Integral T io y → ∀ (χ : Sp T.V ⟶ GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.genFibre Y), χ ≫ pullback.snd _ _ = spMap φ → (letI := io.toAlgebra; GlobalTheory.AllWt.ptF y ≫ Y.jQ = spMap (algebraMap T.V T.Fr) ≫ χ) → ∀ (τ : E →+* ℂ) (n : ℕ) (hn : Dw.mult τ = n), ∃ v : Fin n → (GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.epsAt (χ ≫ pullback.fst _ _) ⟶ Y.t.G), GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.IsEigenBasis Y.t.act (χ ≫ pullback.fst _ _) (GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.chr c τ φ) v ∧ ∀ i, (letI := io.toAlgebra; SameVec Y y (y.u τ (Fin.cast hn.symm i)) (spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR (algebraMap T.V T.Fr)) ≫ (v i).left)) := by
  intro E _ _ _ H Dw l Xo c Y T io φ hφ y hI χ hχ1 hχ2 τ n hn
  subst hn
  letI := io.toAlgebra
  obtain ⟨G, t', m1, m2, ⟨ub, htan, heig, hbas, hu⟩, -⟩ := hI
  obtain ⟨t, ⟨m⟩⟩ := GlobalTheory.ModFam.exists_sabPull (χ ≫ pullback.fst _ _) Y.t
  have hx : GlobalTheory.AllWt.ptF y ≫ pullback.fst _ _ = y.x := pullback.lift_fst _ _ _
  let mK : SABMap t' Xo.univ.t (GlobalTheory.AllWt.ptF y ≫ pullback.fst _ _) := ReciprocityTheory.ChartRestriction.G.PullbackSections.sabMapCast m1 hx.symm
  obtain ⟨a, mF, hF0, hFm⟩ := GlobalTheory.CuspFrom.exists_genIdent Y hχ2 mK m
  obtain ⟨ψ, hψ, -⟩ := GlobalTheory.ModelUniqueChecks.existsUnique_map T.V T.Fr G t t' m2 a
  obtain ⟨nC, hnC⟩ := sabComp pullCubComp E H _ _ _ Y.t t G (χ ≫ pullback.fst _ _) (𝟙 _) m ψ
  let n' : SABMap G Y.t (χ ≫ pullback.fst _ _) := ReciprocityTheory.ChartRestriction.G.PullbackSections.sabMapCast nC (Category.id_comp _)
  obtain ⟨v, hv, hvl⟩ := _root_.GlobalTheory.IntEigTransport.transport E H l c T io φ hφ G Y.X Y.t (χ ≫ pullback.fst _ _) n' τ _ (ub τ) (htan τ)
    (heig τ) (hbas τ)
  refine ⟨v, hv, fun i => ?_⟩
  obtain ⟨u', hu1, hu2⟩ := hu τ i
  have hmono : Mono (spMap (algebraMap T.V T.Fr)) := by
    have : Epi (CommRingCat.ofHom (algebraMap T.V T.Fr)) := IsLocalization.epi (nonZeroDivisors T.V) T.Fr
    exact Scheme.Spec.map_mono (CommRingCat.ofHom _).op
  have hbase : spMap (dualMap (algebraMap T.V T.Fr)) ≫ (epsOver T.V T.V).hom =
      spMap (algebraMap T.Fr (DualNumber T.Fr)) ≫ spMap (algebraMap T.V T.Fr) := by
    show spMap (dualMap (algebraMap T.V T.Fr)) ≫ spMap ((algebraMap T.V (DualNumber T.V)).comp (algebraMap T.V T.V)) = _
    rw [GlobalTheory.ShFam.OpenReg.spMap_comp, GlobalTheory.ShFam.OpenReg.spMap_comp]
    congr 1
    ext x <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  have hut : u' ≫ t'.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) ≫ 𝟙 _ := by
    rw [Category.comp_id]
    apply (cancel_mono (spMap (algebraMap T.V T.Fr))).1
    rw [Category.assoc, ← m2.cart.1.w, ← Category.assoc, hu2, Category.assoc, Over.w (ub τ i), hbase]
  have htan' : IsTanAtG t' (𝟙 _) u' := by
    have h1 := (GlobalTheory.ShFam.OpenReg.tan_iff m1 (Category.id_comp y.x) hut).1
    rw [hu1] at h1
    exact h1 (y.tan τ i)
  refine ⟨u' ≫ mF.φ, (GlobalTheory.ShFam.OpenReg.tan_iff mF (Category.id_comp _) hut).2 htan', ?_, ?_⟩
  · rw [Category.assoc, hF0, ReciprocityTheory.ChartRestriction.G.PullbackSections.sabMapCast_φ, hu1]
    rfl
  · rw [Category.assoc, hFm, ← hψ, hvl i, ReciprocityTheory.ChartRestriction.G.PullbackSections.sabMapCast_φ, hnC]
    simp only [← Category.assoc]
    rw [hu2]
    rfl

end GlobalTheory.IntFrameLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineSectionsExternalTensorPowerFibre
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
namespace GlobalTheory.BoxLine

theorem exists_isPullback_pow {S S' : Scheme.{0}} (g : S' ⟶ S) (G : Over S) (A B : Over S')
    (φ₀ : A.left ⟶ G.left) (h : IsPullback φ₀ A.hom G.hom g) (N : ℕ) (q : Fin N → (B ⟶ A))
    (hl : IsLimit (Fan.mk B q)) :
    ∃ φ : B.left ⟶ (pow G N).left, IsPullback φ B.hom (pow G N).hom g ∧
      ∀ k, φ ≫ pr G N k = (q k).left ≫ φ₀ := by
  let ψ : Over.mk (B.hom ≫ g) ⟶ pow G N := Pi.lift fun k =>
    Over.homMk ((q k).left ≫ φ₀) (by
      simp only [Over.mk_hom, Category.assoc]
      rw [h.w, ← Category.assoc, Over.w])
  have hψ : ∀ k, ψ.left ≫ pr G N k = (q k).left ≫ φ₀ := fun k => by
    have : ψ ≫ Pi.π (fun _ => G) k = _ := Pi.lift_comp_π _ k
    exact congrArg (fun t => Over.Hom.left t) this
  have hw : ψ.left ≫ (pow G N).hom = B.hom ≫ g := Over.w ψ
  have hpr : ∀ k, pr G N k ≫ G.hom = (pow G N).hom := fun k => Over.w (Pi.π (fun _ => G) k)
  refine ⟨ψ.left, ⟨⟨hw⟩, ⟨?_⟩⟩, hψ⟩
  let c : ∀ s : PullbackCone (pow G N).hom g, Fin N → (Over.mk s.snd ⟶ A) := fun s k =>
    Over.homMk (h.lift (s.fst ≫ pr G N k) s.snd (by rw [Category.assoc, hpr, s.condition]))
      (h.lift_snd _ _ _)
  have hc : ∀ s k, (c s k).left ≫ φ₀ = s.fst ≫ pr G N k := fun s k => h.lift_fst _ _ _
  let m : ∀ s : PullbackCone (pow G N).hom g, Over.mk s.snd ⟶ B := fun s =>
    hl.lift (Fan.mk _ (c s))
  have hm : ∀ s k, (m s).left ≫ (q k).left = (c s k).left := fun s k =>
    congrArg (fun t => Over.Hom.left t) (hl.fac (Fan.mk _ (c s)) ⟨k⟩)
  refine PullbackCone.IsLimit.mk _ (fun s => (m s).left) ?_ ?_ ?_
  · intro s
    have hs : (m s).left ≫ B.hom = s.snd := Over.w (m s)
    let u : Over.mk (s.snd ≫ g) ⟶ pow G N := Over.homMk ((m s).left ≫ ψ.left) (by
      simp only [Over.mk_hom, Category.assoc]
      rw [hw, ← Category.assoc, hs])
    let v : Over.mk (s.snd ≫ g) ⟶ pow G N := Over.homMk s.fst s.condition
    have huv : u = v := by
      refine Pi.hom_ext _ _ fun k => ?_
      ext1
      change ((m s).left ≫ ψ.left) ≫ pr G N k = s.fst ≫ pr G N k
      rw [Category.assoc, hψ, ← Category.assoc, hm, hc]
    exact congrArg (fun t => Over.Hom.left t) huv
  · intro s
    exact Over.w (m s)
  · intro s t h1 h2
    let u : Over.mk s.snd ⟶ B := Over.homMk t h2
    have : u = m s := by
      refine hl.uniq (Fan.mk _ (c s)) u ?_
      rintro ⟨k⟩
      ext1
      change t ≫ (q k).left = (c s k).left
      refine h.hom_ext ?_ ?_
      · rw [hc, Category.assoc, ← hψ, ← Category.assoc, h1]
      · rw [Category.assoc, Over.w, h2]
        exact (Over.w (c s k)).symm
    exact congrArg (fun t => Over.Hom.left t) this


open GlobalTheory.CechPic in
theorem cls_pull_box {S : Scheme.{0}} (G : Over S) (L : LB G.left) (hL : L.IsLB) (N : ℕ)
    {X : Scheme.{0}} (φ : X ⟶ (pow G N).left) (h : ((boxLB G L N).pull φ).IsLB) :
    cls ((boxLB G L N).pull φ) h = ∑ k, pull (φ ≫ pr G N k) (cls L hL) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [cls_pull (LB.isLB_linComb hL _ _), cls_linComb hL, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [one_smul, pull_comp]

theorem isLB_triv (X : Scheme.{0}) : (LB.triv X).IsLB :=
  ⟨by simp, fun _ => map_one _, fun _ _ _ => by simp⟩


open GlobalTheory.CechPic in
theorem sections_line : ∀ (V K : Type) [CommRing V] [Field K] (f : V →+* K) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (rig : LB.Gen (L.pull (eSec G))) (θ : L.Sec) (n : ℕ) (w : Fin n → (epsR V ⟶ G)) (x : KeyIn K), L.IsLB → IsFibreOf x G L rig θ w f → ∀ N : ℕ, ∃ (X' : Scheme.{0}) (p' : X' ⟶ Sp K) (φ : X' ⟶ (pow G N).left) (L' : LB X') (b : L'.Sec), IsPullback φ p' (pow G N).hom (spMap f) ∧ L'.IsLB ∧ LBIso L' ((boxLB G L N).pull φ) ∧ ∀ s : L'.Sec, ∃ a : K, ∀ i, s.f i = constFn p' _ a * b.f i := by
  intro V K _ _ f G _ _ L rig θ n w x hL hx N
  obtain ⟨φ₀, he, e, hg, F, hpb, hegen, -⟩ := hx
  have hbox : ∀ {X : Scheme.{0}} (φ : X ⟶ (pow G N).left), ((boxLB G L N).pull φ).IsLB :=
    fun φ => LB.isLB_linComb (LB.isLB_linComb hL _ _) _ _
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · obtain ⟨φ, hφ, -⟩ := exists_isPullback_pow (spMap f) G x.P.A (Over.mk (𝟙 (Sp K))) φ₀ hpb.1 0
      (fun k => k.elim0)
      (Fan.IsLimit.mk _ (fun s => Over.mkIdTerminal.from _) (fun _ k => k.elim0)
        (fun _ _ _ => Over.mkIdTerminal.hom_ext _ _))
    refine ⟨Sp K, 𝟙 _, φ, LB.triv _, ⟨fun _ => 1, fun _ _ => by simp⟩, hφ, isLB_triv _, ?_, ?_⟩
    · rw [iso_triv_iff, ← cls_eq_zero_iff (hbox φ), cls_pull_box G L hL]
      simp
    · intro s
      refine ⟨(Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (s.f PUnit.unit), fun i => ?_⟩
      obtain rfl : i = PUnit.unit := rfl
      have h0 : ∀ (h : (⊤ : (Sp K).Opens) ≤ ⊤) (t : Γ(Sp K, ⊤)),
          ((Sp K).presheaf.map (homOfLE h).op).hom t = t := fun h t => by
        rw [show homOfLE h = 𝟙 _ from rfl, op_id, CategoryTheory.Functor.map_id]
        rfl
      simp [constFn, Scheme.Hom.appLE]
      exact (h0 _ _).symm
  · obtain ⟨y, p, -⟩ := GlobalTheory.KeyPow.exists_isKeyPow K x N hN
    obtain ⟨φ, hφ, hc⟩ := exists_isPullback_pow (spMap f) G x.P.A y.P.A φ₀ hpb.1 N p.pr p.lim
    obtain ⟨b, hb⟩ := principalPolarisation_exists_unique_section GlobalTheory.firstFiveLaws.2.1.secTwist y.P
    refine ⟨y.P.A.left, y.P.A.hom, φ, y.P.L, b, hφ, y.P.isLB, ?_, fun s => (hb s).exists⟩
    have h1 : cls x.P.L x.P.isLB = pull φ₀ (cls L hL) := by
      rw [← cls_pull hL φ₀ (LB.isLB_linComb hL _ _), cls_eq_iff]
      exact ⟨e, hegen⟩
    have h2 : cls y.P.L y.P.isLB
        = cls (Out.boxLB x.P.L p.pr) (LB.isLB_linComb x.P.isLB _ _) := by
      rw [cls_eq_iff]
      exact ⟨p.w, p.w_gen⟩
    rw [← cls_eq_iff y.P.isLB (hbox φ), cls_pull_box G L hL, h2, cls_linComb x.P.isLB]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [one_smul, hc, pull_comp, h1]

end GlobalTheory.BoxLine
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowerSeriesOfNoPoleAwayUniformizerXStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_powerSeries_of_no_pole_away_uniformizer_X : ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (ϖ : A), Irreducible ϖ → ∀ (k : A →+* ℂ), Function.Injective k → ∀ (S : Type) [CommRing S] [Algebra (PowerSeries A) S] [IsLocalization.Away (PowerSeries.C ϖ * PowerSeries.X : PowerSeries A) S] (ι : S →+* ℂ⸨X⸩), (∀ s : PowerSeries A, ι (algebraMap _ S s) = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.map k s)) → ∀ v : S, ι v ∈ (HahnSeries.ofPowerSeries ℤ ℂ).range → (∃ s t : PowerSeries A, ¬ PowerSeries.C ϖ ∣ t ∧ v * algebraMap _ S t = algebraMap _ S s) → ∃ s : PowerSeries A, v = algebraMap _ S s := by
  first | exact @GlobalTheory.PowerSeriesNoPole.exists_eq_algebraMap | exact GlobalTheory.PowerSeriesNoPole.exists_eq_algebraMap | (intros; apply GlobalTheory.PowerSeriesNoPole.exists_eq_algebraMap <;> assumption)
end

