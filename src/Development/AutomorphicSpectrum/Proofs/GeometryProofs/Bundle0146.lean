module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLatticeVectorBundle
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0130
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLatticeConstantRank
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0141
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0144
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0058
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0140
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0096
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0062
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0145
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0019
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0078
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0143
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0023
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeDominantCompat
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0041
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0076
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.NonemptyEquivOfCardHom
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RelOfTorsion
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0024
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0049
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle0012
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0008
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0017
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.FramedPointSpecialization
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0002
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Farsharp

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentPointValueHolomorphic
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LocFrames

open GlobalTheory.CompanionTheory.Ar.LieVB GlobalTheory.CompanionTheory.Ar.LieTangent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem exists_lift_vec (Y : Model Xo c β) {A : Type} [CommRing A] (f : Sp A ⟶ Xo.XF c)
    (t : epsAt (f ≫ Y.j) ⟶ Y.t.G) :
    ∃ vR : epsAt (under f) ⟶ Xo.univ.t.G, ∀ (χ : A →+* ℂ) (v : epsAt (under (spMap χ ≫ f)) ⟶ Xo.univ.t.G)
      (v' : epsAt ((spMap χ ≫ f) ≫ Y.j) ⟶ Y.t.G), v.left = spMap (dualMap χ) ≫ vR.left →
      v'.left = spMap (dualMap χ) ≫ t.left → SameVec Y (spMap χ ≫ f) v v' := by
  have hp : IsPullback Y.m0.toSABMap.φ Y.oF.t.G.hom Xo.univ.t.G.hom (pullback.fst _ _) := Y.m0.cart.1
  have hq : IsPullback Y.m.φ Y.oF.t.G.hom Y.t.G.hom Y.j := Y.m.cart.1
  have ht : t.left ≫ Y.t.G.hom = (spMap (algebraMap A (DualNumber A)) ≫ f) ≫ Y.j := by
    rw [Category.assoc]; exact Over.w t
  let u := hq.lift _ _ ht
  have hu : u ≫ Y.oF.t.G.hom = spMap (algebraMap A (DualNumber A)) ≫ f := hq.lift_snd _ _ ht
  refine ⟨Over.homMk (u ≫ Y.m0.toSABMap.φ) ?_, fun χ v v' hv hv' => ?_⟩
  · change (u ≫ Y.m0.toSABMap.φ) ≫ Xo.univ.t.G.hom = spMap (algebraMap A (DualNumber A)) ≫ f ≫ pullback.fst _ _
    rw [Category.assoc, hp.w, ← Category.assoc, hu, Category.assoc]
  refine ⟨spMap (dualMap χ) ≫ u, ?_, ?_, ?_⟩
  · rw [Category.assoc, hu, ← Category.assoc, ← Category.assoc]
    congr 1
    exact spec_dual_alg χ
  · rw [hv]; simp
  · rw [hv', Category.assoc]
    congr 1
    exact hq.lift_fst _ _ ht

theorem isEigFrame_of_values {Y : Model Xo c β} {U : Set (Xo.XF c)} (Z : CptOver Y U) (σ : c.F →+* ℂ)
    (y : Sp ℂ ⟶ Xo.XF c) (τ : E →+* ℂ) (n : ℕ) (e : Fin n → Z.V) (v : Vecs y n)
    (v' : Fin n → (epsAt (y ≫ Y.j) ⟶ Y.t.G)) (h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j))
    (hO : ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) (hy : y ≫ pullback.snd _ _ = spMap σ)
    (hL : LieMult Xo.univ.t.act (under y) (σ.comp (tauIn c τ)) n)
    (h3 : ∃ g : ℕ, ∃ b : Fin g → Z.V, Z.M.lat.IsFrameAt b ⟨centre (y ≫ Y.j), h⟩ ∧ ∃ S : Finset (Fin g),
      Z.eig τ ⟨centre (y ≫ Y.j), h⟩ = Submodule.span (regAt _ ⟨centre (y ≫ Y.j), h⟩) (b '' S))
    (hf : (Z.eig τ).IsFrameAt e ⟨centre (y ≫ Y.j), h⟩)
    (hval : ∀ i, Z.M.ValAt (y ≫ Y.j) (e i) (v' i)) (hsame : ∀ i, SameVec Y y (v i) (v' i)) :
    IsEigFrame Xo.univ.t.act (under y) (σ.comp (tauIn c τ)) v := by
  haveI : Smooth Y.t.G.hom := Y.t.semi.smooth
  obtain ⟨EC, _, _, N, ρ, hρ, hD⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.exists_lieModel_tied_isEigFrame E H D l Xo c O β Y y
  have hex : ∀ i, ∃ w, N.pt w = v' i := fun i => N.onto _ (hval i).isTanAt
  choose w hw using hex
  obtain ⟨g, b, hb, S, hS⟩ := h3
  have hval' : ∀ i, Z.M.ValAt (y ≫ Y.j) (e i) (N.pt (w i)) := fun i => by rw [hw]; exact hval i
  refine hD _ n v w hL (fun i => by rw [hw]; exact hsame i) ?_ fun i => ?_
  · exact _root_.GlobalTheory.CompanionTheory.Ar.values_frame_sublattice_linearIndependent Y.X Y.t.G Z.Ω (Z.ξ₀ ≫ Y.j) Z.V Z.M ℂ (y ≫ Y.j) h EC N g n b S e (Z.eig τ) w Z.gen hb hS hf
      hval'
  · have hmem : e i ∈ Z.eig τ ⟨centre (y ≫ Y.j), h⟩ := by
      rw [hf.2]
      exact Submodule.subset_span ⟨i, rfl⟩
    exact _root_.GlobalTheory.CompanionTheory.Ar.FramesEig.mem_eigSp_of_valAt E H D l Xo c O β Y U Z σ y EC N ρ (tauIn c τ) (e i) (w i) hO hy hρ hmem.2 (hval' i)

theorem ring_eq {X : Scheme.{0}} {R : Type} [CommRing R] (x : Sp R ⟶ X) [Mono x] (z : Sp ℂ ⟶ X)
    (ψ : R →+* X.presheaf.stalk (centre z)) (hψ : spMap ψ ≫ x = X.fromSpecStalk (centre z)) (f : R →+* ℂ)
    (hf : spMap f ≫ x = z) : (Scheme.stalkClosedPointTo z).hom.comp ψ = f := by
  have h1 : spMap ((Scheme.stalkClosedPointTo z).hom.comp ψ) ≫ x = spMap f ≫ x := by
    have e1 : spMap ((Scheme.stalkClosedPointTo z).hom.comp ψ) =
        spMap (Scheme.stalkClosedPointTo z).hom ≫ spMap ψ := by
      simp only [spMap, ← Spec.map_comp]; rfl
    rw [e1, Category.assoc, hψ, hf]
    exact spec_centre z
  exact congrArg (fun g => g.hom) (Spec.map_injective ((cancel_mono x).1 h1))

theorem lieMult_at (y : Sp ℂ ⟶ Xo.XF c) (σ : c.F →+* ℂ) (τ : E →+* ℂ) (hy : y ≫ pullback.snd _ _ = spMap σ)
    (hτ : τ (H.rt : E) = H.rt0) :
    LieMult Xo.univ.t.act (under y) (σ.comp (tauIn c τ)) D.p ∧
      LieMult Xo.univ.t.act (under y) (σ.comp (tauIn c (ComplexEmbedding.conjugate τ))) D.q := by
  have hs : under y ≫ Xo.s = spMap (σ.comp (IntermediateField.inclusion c.le).toRingHom) := by
    change (y ≫ pullback.fst _ _) ≫ Xo.s = _
    rw [Category.assoc, pullback.condition, ← Category.assoc, hy]
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hdet := (Xo.univ.geom ℂ (under y) _ hs).1
  have e1 : tauIn c τ H.rt = IntermediateField.inclusion c.le (baseKA l).ρ := Subtype.ext hτ
  have e2 : tauIn c (ComplexEmbedding.conjugate τ) H.rt = -IntermediateField.inclusion c.le (baseKA l).ρ := by
    apply Subtype.ext
    show starRingEnd ℂ (τ (H.rt : E)) = - H.rt0
    rw [hτ]
    exact GlobalTheory.CompanionTheory.Ar.EigRank.rt0_conj_neg_ne_zero H.d_prime.pos H.sqrt_neg_disc_sq
  refine ⟨(hdet _).1 ?_, (hdet _).2 ?_⟩
  · simp only [RingHom.comp_apply, e1]
    rfl
  · simp only [RingHom.comp_apply, e2, map_neg]
    intro h
    have h0 : σ (IntermediateField.inclusion c.le (baseKA l).ρ) = 0 := by
      have h2 : (2 : ℂ) * σ (IntermediateField.inclusion c.le (baseKA l).ρ) = 0 := by
        have : -σ (IntermediateField.inclusion c.le (baseKA l).ρ) =
          σ (IntermediateField.inclusion c.le (baseKA l).ρ) := h
        linear_combination -this
      exact (mul_eq_zero.mp h2).resolve_left two_ne_zero
    have h1 : ((baseKA l).ρ : ℂ) = 0 := by
      have := (map_eq_zero σ).1 h0
      exact congrArg Subtype.val this
    have h3 : (H.rt0 : ℂ) = 0 := h1
    have h4 := H.sqrt_neg_disc_sq
    rw [h3] at h4
    have h5 : ((H.d : ℕ) : ℂ) = 0 := by simpa using h4.symm
    exact H.d_prime.ne_zero (Nat.cast_eq_zero.mp h5)

theorem exists_local_eigenframes : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (σ : c.F →+* ℂ) (y₀ : Sp ℂ ⟶ Xo.XF c), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → τ (H.rt : E) = H.rt0 → y₀ ≫ pullback.snd _ _ = spMap σ → Set.range y₀ ⊆ U → ∃ (V₀ : (Xo.XF c).Opens) (hV₀ : IsAffineOpen V₀) (c₁ : Fin D.p → Z.V) (c₂ : Fin D.q → Z.V) (vR : Fin D.p → (epsAt (under hV₀.fromSpec) ⟶ Xo.univ.t.G)) (wR : Fin D.q → (epsAt (under hV₀.fromSpec) ⟶ Xo.univ.t.G)), ⊤ ≤ y₀ ⁻¹ᵁ V₀ ∧ LinearIndependent Z.Ω c₁ ∧ Submodule.span Z.Ω (Set.range c₁) = eigSp Z.ρ (Z.inc.comp (tauIn c τ)) ∧ LinearIndependent Z.Ω c₂ ∧ Submodule.span Z.Ω (Set.range c₂) = eigSp Z.ρ (Z.inc.comp (tauIn c (ComplexEmbedding.conjugate τ))) ∧ ∀ (χ : Γ(Xo.XF c, V₀) →+* ℂ) (v : Vecs (spMap χ ≫ hV₀.fromSpec) D.p) (w : Vecs (spMap χ ≫ hV₀.fromSpec) D.q), (spMap χ ≫ hV₀.fromSpec) ≫ pullback.snd _ _ = spMap σ → Set.range (spMap χ ≫ hV₀.fromSpec) ⊆ U → (∀ a, (v a).left = spMap (dualMap χ) ≫ (vR a).left) → (∀ j, (w j).left = spMap (dualMap χ) ≫ (wR j).left) → IsFramed U τ σ (spMap χ ≫ hV₀.fromSpec) v w ∧ (∀ i, ∃ v', Z.M.ValAt ((spMap χ ≫ hV₀.fromSpec) ≫ Y.j) (c₁ i) v' ∧ SameVec Y (spMap χ ≫ hV₀.fromSpec) (v i) v') ∧ ∀ j, ∃ w', Z.M.ValAt ((spMap χ ≫ hV₀.fromSpec) ≫ Y.j) (c₂ j) w' ∧ SameVec Y (spMap χ ≫ hV₀.fromSpec) (w j) w' := by
  intro E _ _ _ H D l Xo c O _ β Y U Z τ σ y₀ hO hτ hy₀ hr₀
  obtain ⟨hv1, hv2, h3, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.isVBOn_eig_genFib E H D l Xo c O β Y U Z τ hO hτ
  haveI : Smooth Y.t.G.hom := Y.t.semi.smooth
  have hsp : ∀ y : Sp ℂ ⟶ Xo.XF c, Set.range y ⊆ U → genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j) := fun y hy => by
    have h1 : genPt Z.ξ₀ ⤳ y (IsLocalRing.closedPoint ℂ) := (Z.closure _).1 (hy ⟨_, rfl⟩)
    have h2 := h1.map Y.j.continuous
    simp only [genPt, centre, Scheme.Hom.comp_apply]
    exact h2
  have hfib : ∀ (y : Sp ℂ ⟶ Xo.XF c) (h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j)),
      (⟨centre (y ≫ Y.j), h⟩ : Cpt (Z.ξ₀ ≫ Y.j)) ∈ Z.genFib := fun y h =>
    ⟨Y.jQ (y (IsLocalRing.closedPoint ℂ)), by
      simp only [Model.j, centre, Scheme.Hom.comp_apply]⟩
  let p₀ : Cpt (Z.ξ₀ ≫ Y.j) := ⟨centre (y₀ ≫ Y.j), hsp y₀ hr₀⟩
  obtain ⟨N₁, hp₁, c₁, hs₁, hf₁⟩ := hv1 p₀ (hfib y₀ _)
  obtain ⟨N₂, hp₂, c₂, hs₂, hf₂⟩ := hv2 p₀ (hfib y₀ _)
  have hc₁ : ∀ i, c₁ i ∈ Z.M.lat p₀ := fun i => by
    have : c₁ i ∈ Z.eig τ p₀ := by
      rw [(hf₁ p₀ (hfib y₀ _) hp₁).2]
      exact Submodule.subset_span ⟨i, rfl⟩
    exact this.1
  have hc₂ : ∀ i, c₂ i ∈ Z.M.lat p₀ := fun i => by
    have : c₂ i ∈ Z.eig (ComplexEmbedding.conjugate τ) p₀ := by
      rw [(hf₂ p₀ (hfib y₀ _) hp₂).2]
      exact Submodule.subset_span ⟨i, rfl⟩
    exact this.1
  obtain ⟨R, _, x, _, F, _, _, MR, e, hpx, hxN, hext⟩ := GlobalTheory.T.local_lie_model_extends Y.X Y.t.G Z.Ω (Z.ξ₀ ≫ Y.j) Z.V Z.M p₀
    (N₁ ⊓ N₂) (Fin D.p ⊕ Fin D.q) (Sum.elim c₁ c₂) ⟨hp₁, hp₂⟩ (by rintro (i | i); exacts [hc₁ i, hc₂ i])
  let W : (Xo.XF c).Opens := Y.j ⁻¹ᵁ x.opensRange
  have hW : y₀ (IsLocalRing.closedPoint ℂ) ∈ W := by
    change Y.j (y₀ (IsLocalRing.closedPoint ℂ)) ∈ x.opensRange
    have : centre (y₀ ≫ Y.j) ∈ x.opensRange := hpx
    simpa only [centre, Scheme.Hom.comp_apply] using this
  obtain ⟨_, ⟨V₀, hV₀, rfl⟩, hyV, hVW⟩ := (Xo.XF c).isBasis_affineOpens.exists_subset_of_mem_open hW W.isOpen
  replace hV₀ : IsAffineOpen V₀ := hV₀
  have hrange : Set.range (hV₀.fromSpec ≫ Y.j) ⊆ Set.range x := by
    rintro _ ⟨t, rfl⟩
    have h1 : hV₀.fromSpec t ∈ V₀ := by
      have : hV₀.fromSpec t ∈ Set.range hV₀.fromSpec := ⟨t, rfl⟩
      rwa [hV₀.range_fromSpec] at this
    exact hVW h1
  obtain ⟨a, ha⟩ : ∃ a : R →+* Γ(Xo.XF c, V₀), spMap a ≫ x = hV₀.fromSpec ≫ Y.j :=
    ⟨(Spec.preimage (IsOpenImmersion.lift x (hV₀.fromSpec ≫ Y.j) hrange)).hom, by
      change Spec.map (CommRingCat.ofHom (Spec.preimage (IsOpenImmersion.lift x _ hrange)).hom) ≫ x = _
      rw [CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]⟩
  let t : Fin D.p ⊕ Fin D.q → (epsAt (hV₀.fromSpec ≫ Y.j) ⟶ Y.t.G) := fun i => epsBase a ha ≫ MR.pt (e i)
  choose vR hvR using fun i => exists_lift_vec Y hV₀.fromSpec (t i)
  refine ⟨V₀, hV₀, c₁, c₂, fun i => vR (Sum.inl i), fun i => vR (Sum.inr i), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Scheme.preimage_eq_top_of_closedPoint_mem (R := CommRingCat.of ℂ) y₀ hyV).ge
  · exact (hf₁ p₀ (hfib y₀ _) hp₁).1
  · exact hs₁
  · exact (hf₂ p₀ (hfib y₀ _) hp₂).1
  · exact hs₂
  intro χ v w hσ hr hv hw
  let y : Sp ℂ ⟶ Xo.XF c := spMap χ ≫ hV₀.fromSpec
  have h := hsp y hr
  let q : Cpt (Z.ξ₀ ≫ Y.j) := ⟨centre (y ≫ Y.j), h⟩
  have hqr : q.1 ∈ x.opensRange := hrange ⟨spMap χ (IsLocalRing.closedPoint ℂ), rfl⟩
  have hqx : (Y.X.fromSpecStalk q.1) (IsLocalRing.closedPoint (Y.X.presheaf.stalk q.1)) ∈ x.opensRange := by
    rw [Scheme.fromSpecStalk_closedPoint]
    exact hqr
  obtain ⟨ψ, hψ⟩ := exists_lift (A := Y.X.presheaf.stalk q.1) x (Y.X.fromSpecStalk q.1) hqx
  have hring : (Scheme.stalkClosedPointTo (y ≫ Y.j)).hom.comp ψ = χ.comp a := by
    refine ring_eq x (y ≫ Y.j) ψ hψ _ ?_
    have e2 : spMap (χ.comp a) = spMap χ ≫ spMap a := by
      simp only [spMap, ← Spec.map_comp]; rfl
    rw [e2, Category.assoc, ha, ← Category.assoc]
  have hχ : spMap χ ≫ hV₀.fromSpec ≫ Y.j = y ≫ Y.j := (Category.assoc _ _ _).symm
  let T : Fin D.p ⊕ Fin D.q → (epsAt (y ≫ Y.j) ⟶ Y.t.G) := fun i => epsBase χ hχ ≫ t i
  have hval : ∀ i, Z.M.ValAt (y ≫ Y.j) (Sum.elim c₁ c₂ i) (T i) := fun i => by
    let vq : epsAt (R := Y.X.presheaf.stalk q.1) (Y.X.fromSpecStalk q.1) ⟶ Y.t.G :=
      epsBase ψ hψ ≫ MR.pt (e i)
    refine ⟨h, vq, hext q ψ hψ i vq rfl, ?_⟩
    change spMap (dualMap χ) ≫ spMap (dualMap a) ≫ (MR.pt (e i)).left =
      spMap (dualMap (Scheme.stalkClosedPointTo (y ≫ Y.j)).hom) ≫ spMap (dualMap ψ) ≫ (MR.pt (e i)).left
    rw [← Category.assoc, ← Category.assoc, spMap_dual_comp, spMap_dual_comp, hring]
  obtain ⟨hL₁, hL₂⟩ := lieMult_at y σ τ hσ hτ
  obtain ⟨g, b, hb, hS⟩ := h3 q (hfib y h)
  have hin : q.1 ∈ N₁ ⊓ N₂ := hxN hqr
  have same : ∀ (i : Fin D.p ⊕ Fin D.q) (u : epsAt (under y) ⟶ Xo.univ.t.G),
      u.left = spMap (dualMap χ) ≫ (vR i).left → SameVec Y y u (T i) := fun i u hu =>
    hvR i χ u (T i) hu rfl
  refine ⟨⟨hσ, hr, ?_, ?_⟩, fun i => ⟨T (Sum.inl i), hval (Sum.inl i), same _ _ (hv i)⟩,
    fun i => ⟨T (Sum.inr i), hval (Sum.inr i), same _ _ (hw i)⟩⟩
  · exact isEigFrame_of_values Z σ y τ D.p c₁ v (fun i => T (Sum.inl i)) h hO.2.2 hσ hL₁ ⟨g, b, hb, hS τ⟩
      (hf₁ q (hfib y h) hin.1) (fun i => hval (Sum.inl i)) (fun i => same _ _ (hv i))
  · exact isEigFrame_of_values Z σ y _ D.q c₂ w (fun i => T (Sum.inr i)) h hO.2.2 hσ hL₂ ⟨g, b, hb, hS _⟩
      (hf₂ q (hfib y h) hin.2) (fun i => hval (Sum.inr i)) (fun i => same _ _ (hw i))

end GlobalTheory.CompanionTheory.Ar.LocFrames
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentSpecializationFieldExt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat
open GlobalTheory.CompanionTheory.Ar.Flat.Rep

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Flat.Rep

theorem lieValAt_spMap {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G] {ξ : Sp Ω ⟶ X}
    {V : Type} [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V) (hξ : IsCptGen ξ) {F F' : Type} [Field F]
    [Field F'] (f : F →+* F') {z : Sp F ⟶ X} {z' : Sp F' ⟶ X} (hz : spMap f ≫ z = z') {e : V}
    {w : epsAt z ⟶ G} {w' : epsAt z' ⟶ G} (hw : w'.left = spMap (dualMap f) ≫ w.left) (h : M.ValAt z e w) :
    M.ValAt z' e w' := by
  letI : Algebra F F' := f.toAlgebra
  subst hz
  obtain ⟨hc, v, hext, hw0⟩ := h
  have hbot : ∀ x : PrimeSpectrum F, x.asIdeal = ⊥ := fun x =>
    (Ideal.eq_bot_or_top _).resolve_right x.isPrime.ne_top
  have hp : (spMap f) (IsLocalRing.closedPoint F') = IsLocalRing.closedPoint F :=
    PrimeSpectrum.ext ((hbot _).trans (hbot _).symm)
  have hcen : GlobalTheory.CompanionTheory.Ar.centre (spMap f ≫ z) = GlobalTheory.CompanionTheory.Ar.centre z := by
    change z ((spMap f) (IsLocalRing.closedPoint F')) = z (IsLocalRing.closedPoint F)
    rw [hp]
  have hc' : GlobalTheory.CompanionTheory.Ar.genPt ξ ⤳ GlobalTheory.CompanionTheory.Ar.centre (spMap f ≫ z) := hcen ▸ hc
  exact GlobalTheory.CompanionTheory.Ar.LieFib.valAt_base M z hc hc' v hext w' w hw hw0

theorem isValFam_spMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (F F' : Type) [Field F] [Field F'] (f : F →+* F') (y : Sp F ⟶ Xo.XF c) (y' : Sp F' ⟶ Xo.XF c), y' = spMap f ≫ y → ∀ (n : ℕ) (b : Fin n → Z.V) (v : Vecs y n) (v' : Vecs y' n), (∀ i, (v' i).left = spMap (dualMap f) ≫ (v i).left) → IsValFam Z y b v → IsValFam Z y' b v' := by
  intro E _ _ _ H D l Xo c O _ β Y U Z F F' _ _ f y y' hy n b v v' hv' hv
  subst hy
  simp only [GlobalTheory.CompanionTheory.Ar.Flat.Rep.IsValFam] at hv ⊢
  intro i
  obtain ⟨u, hval, t, ht1, ht2, ht3⟩ := hv i
  have hzz : spMap f ≫ (y ≫ Y.j) = (spMap f ≫ y) ≫ Y.j := (Category.assoc _ _ _).symm
  refine ⟨GlobalTheory.CompanionTheory.Ar.LieTangent.epsBase f hzz ≫ u, ?_, ?_⟩
  · exact lieValAt_spMap Z.M Z.gen f hzz rfl hval
  · simp only [GlobalTheory.CompanionTheory.Ar.Flat.SameVec]
    refine ⟨spMap (GlobalTheory.CompanionTheory.Ar.dualMap f) ≫ t, ?_, ?_, ?_⟩
    · rw [Category.assoc, ht1]
      simp only [ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap]
      rw [← Category.assoc, GlobalTheory.CompanionTheory.Ar.LieTangent.spec_dual_alg, Category.assoc]
    · rw [Category.assoc, ht2, hv' i]
    · rw [Category.assoc, ht3]
      try rfl

end GlobalTheory.CompanionTheory.Ar.Flat.Rep
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConstantsCompatibleGeneric
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HcLie

theorem mem_eigSp_iff {R : Type} [CommRing R] {V : Type} [AddCommGroup V] [Module R V] {O : Type} [CommRing O]
    (ρ : O →+* Module.End R V) (σ : O →+* R) (e : V) :
    e ∈ eigSp ρ σ ↔ ∀ a, ρ a e = σ a • e := by
  simp [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

theorem exists_lie_eig : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (y₀ : Sp Ω ⟶ Xo.XF c) (cst₀ : c.F →+* 𝔐.Ω₀) (y₁ : Sp 𝔐.Ω₀ ⟶ Xo.XF c), 𝔐.ξ ≫ 𝔐.f = y₀ ≫ Y.j → 𝔐.ξ₀ = y₁ ≫ Y.j → 𝔐.ξ₀ ≫ Y.s = spMap (cst₀.comp (algebraMap (𝓞 c.F) c.F)) → 𝔐.fn.comp cst₀ = 𝔐.cst → ∃ (Li₀ : Type) (_ : AddCommGroup Li₀) (_ : Module 𝔐.Ω₀ Li₀) (M₀ : LieModel Y.t.G 𝔐.ξ₀ Li₀) (j : Li₀ →+ 𝔐.Li) (V₀ : CMType H ⊕ CMType H → Submodule 𝔐.Ω₀ Li₀) (b : ∀ s, Fin (labelRk D s) → Li₀), (∀ e, (𝔐.M.pt (j e)).left ≫ 𝔐.m.φ = spMap (dualMap 𝔐.fn) ≫ (M₀.pt e).left) ∧ (∀ (a : 𝔐.Ω₀) e, j (a • e) = 𝔐.fn a • j e) ∧ (∀ s e, e ∈ V₀ s ↔ j e ∈ 𝔐.Vgen s) ∧ (∀ s, LinearIndependent 𝔐.Ω₀ (b s) ∧ Submodule.span 𝔐.Ω₀ (Set.range (b s)) = V₀ s) ∧ (∀ s, LinearIndependent Ω fun k => j (b s k)) ∧ ∀ s, Submodule.span Ω (Set.range fun k => j (b s k)) = 𝔐.Vgen s := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K _ J y 𝔐 y₀ cst₀ y₁ hy hy₁ hs₀ hcst
  classical
  haveI : CharZero 𝔐.Ω₀ := (RingHom.charZero_iff 𝔐.fn.injective).2 inferInstance
  obtain ⟨Li₀, _, _, ⟨M₀⟩⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists _ Y.t.G 𝔐.Ω₀ 𝔐.ξ₀
  obtain ⟨ρ₀, hρ₀, -⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists_unique_act _ Y.t.G 𝔐.Ω₀ 𝔐.ξ₀ Li₀ M₀ (𝓞 E) Y.t.act.act
    Y.t.act.hom Y.t.act.one Y.t.act.mul Y.t.act.add
  obtain ⟨j, hj, hsl, hli, -, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.LiePullSab.lie_pull_lat E H Y.X Y.t 𝔐.X 𝔐.t 𝔐.f 𝔐.m 𝔐.Ω₀ Ω 𝔐.ξ₀ 𝔐.ξ 𝔐.fn Li₀ 𝔐.Li M₀ 𝔐.M
    𝔐.gen₀ 𝔐.tie.gen 𝔐.fn_over
  obtain ⟨m₀, -⟩ := GlobalTheory.CompanionTheory.Ar.exists_sabMap_id E H Y.X Y.t
  obtain ⟨hfd₀, hrk₀⟩ := _root_.GlobalTheory.CompanionTheory.Ar.EigRank.eig_finrank_label E H D l Xo c Y Y.X 𝔐.Ω₀ 𝔐.ξ₀ (𝟙 _) y₁ Y.t m₀ Li₀ M₀ ρ₀ cst₀
    (by rw [Category.comp_id]; exact hy₁) (by rw [Category.id_comp]; exact hs₀) hρ₀
  obtain ⟨hfd, hrk⟩ := _root_.GlobalTheory.CompanionTheory.Ar.EigRank.eig_finrank_label E H D l Xo c Y 𝔐.X Ω 𝔐.ξ 𝔐.f y₀ 𝔐.t 𝔐.m 𝔐.Li 𝔐.M 𝔐.ρ 𝔐.cst hy 𝔐.cst_over 𝔐.act
  have hρj : ∀ (a : 𝓞 E) e, j (ρ₀ a e) = 𝔐.ρ a (j e) := by
    intro a e
    apply 𝔐.M.inj
    refine Over.OverMorphism.ext (𝔐.m.cart.1.hom_ext ?_ ?_)
    · rw [hj, hρ₀ a e, 𝔐.act a (j e), Over.comp_left, Over.comp_left, Category.assoc, 𝔐.m.act, ← Category.assoc,
        ← Category.assoc (𝔐.M.pt (j e)).left]
      exact congrArg (· ≫ (Y.t.act.act a).left) (hj e).symm
    · rw [Over.w, Over.w]
  have hinj : Function.Injective j := by
    refine (injective_iff_map_eq_zero j).2 fun v hv => by_contra fun h0 => ?_
    exact (hli 1 (fun _ => v) (linearIndependent_unique_iff.2 h0)).ne_zero 0 hv
  have hσ : ∀ s (a : 𝓞 E), 𝔐.fn ((cst₀.comp (labelEmb c s)) a) = 𝔐.emb s a := by
    intro s a
    show (𝔐.fn.comp cst₀) (labelEmb c s a) = 𝔐.cst (labelEmb c s a)
    rw [hcst]
  let V₀ : CMType H ⊕ CMType H → Submodule 𝔐.Ω₀ Li₀ := fun s => eigSp ρ₀ (cst₀.comp (labelEmb c s))
  have hV : ∀ s e, e ∈ V₀ s ↔ j e ∈ 𝔐.Vgen s := by
    intro s e
    show e ∈ eigSp ρ₀ _ ↔ j e ∈ eigSp 𝔐.ρ _
    rw [mem_eigSp_iff, mem_eigSp_iff]
    refine forall_congr' fun a => ?_
    rw [← hρj, ← hσ, ← hsl]
    exact hinj.eq_iff.symm
  let B : ∀ s, Module.Basis (Fin (labelRk D s)) 𝔐.Ω₀ (V₀ s) := fun s => Module.finBasisOfFinrankEq _ _ (hrk₀ s)
  let b : ∀ s, Fin (labelRk D s) → Li₀ := fun s k => (B s k : Li₀)
  have hbli : ∀ s, LinearIndependent 𝔐.Ω₀ (b s) := fun s =>
    (B s).linearIndependent.map' (V₀ s).subtype (Submodule.ker_subtype _)
  have hbsp : ∀ s, Submodule.span 𝔐.Ω₀ (Set.range (b s)) = V₀ s := by
    intro s
    have h : Set.range (b s) = (V₀ s).subtype '' Set.range (B s) := by
      rw [← Set.range_comp]
      rfl
    rw [h, ← Submodule.map_span, (B s).span_eq, Submodule.map_top, Submodule.range_subtype]
  have hjli : ∀ s, LinearIndependent Ω fun k => j (b s k) := fun s => hli _ _ (hbli s)
  refine ⟨Li₀, inferInstance, inferInstance, M₀, j, V₀, b, hj, hsl, hV, fun s => ⟨hbli s, hbsp s⟩, hjli, fun s => ?_⟩
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact (hV s _).1 ((hbsp s) ▸ Submodule.subset_span ⟨k, rfl⟩)
  · rw [finrank_span_eq_card (hjli s), Fintype.card_fin]
    exact (hrk s).symm

end GlobalTheory.CompanionTheory.Ar.HcLie
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualNumberSectionDerivationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_number_section_derivation : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (C : Type) [CommRing C] (y : Sp C ⟶ S) (L : Type) [AddCommGroup L] [Module C L] (M : LieModel G y L) (W : G.left.Opens) (h : ∀ l, ⊤ ≤ (M.pt l).left ⁻¹ᵁ W) (s : Γ(G.left, W)), ∃ D : L →ₗ[C] C, ∀ l, D l = (secVal (B := DualNumber C) (M.pt l).left W (h l) s).snd := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HtPull.exists_linear_snd | exact GlobalTheory.CompanionTheory.Ar.HtPull.exists_linear_snd | (intros; apply GlobalTheory.CompanionTheory.Ar.HtPull.exists_linear_snd <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsDualToInvariantDifferentials
section
namespace GlobalTheory.CompanionTheory.Ar.BT

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open _root_.GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

theorem valAt_sub_one {B : Type} [CommRing B] {X : Scheme.{0}} (y : Spec (CommRingCat.of B) ⟶ X) (a : Γ(X, ⊤)) :
    valAt y ⊤ le_top (a - 1) = valAt y ⊤ le_top a - 1 := by
  simp [valAt]

theorem omega_isDerAtOne : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → Smooth G.hom → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L), ∃ θ : Module.Dual R L →ₗ[R] omega (Γ.btOrder ⊤), (Function.Surjective θ ∧ ∀ (f : augIdeal (Γ.btOrder ⊤)) (w : Module.Dual R L), θ w = (augIdeal (Γ.btOrder ⊤)).toCotangent f ↔ Γ.IsDerAtOne i M N (f.1.1 : T → R) w) ∧ (∀ w, θ w = 0 ↔ ∃ u, w = N • u) ∧ ∀ (χ : T →* Rˣ) (w : Module.Dual R L), Γ.IsHT i M N χ w → θ w = dlogChar (Γ.btOrder ⊤) χ := by
  intro R _ _ _ _ T _ _ Γ S G _ _ x N i ht hsm L _ _ M
  obtain ⟨θ, hsurj, hker, hpin⟩ := Tan.omega_canon R T Γ S G x N i ht hsm L M
  obtain ⟨j, hj, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.BT.exists_unique_emb_btOrder_top R T Γ
  have hex := fun e : L => (TanLift.tangent_mod_torsion R T Γ S G x N i ht L M e).exists
  have hsec : ∀ f : Γ.btOrder ⊤, ∃ s, Γ.HasValues s (f : T → R) := fun f =>
    ⟨j.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (Γ.btOrder ⊤))).inv.hom f), fun t =>
      ValEmb.valAt_pull j (Γ.pt t).left _ (hj.pt t) f⟩
  have pin : ∀ (f : augIdeal (Γ.btOrder ⊤)) (w : Module.Dual R L),
      θ w = (augIdeal (Γ.btOrder ⊤)).toCotangent f ↔ Γ.IsDerAtOne i M N (f.1.1 : T → R) w := by
    intro f w
    have h0 : (f.1.1 : T → R) 1 = 0 := f.2
    constructor
    · intro h
      obtain ⟨s, hs⟩ := hsec f.1
      refine ⟨s, hs, fun e => ?_⟩
      obtain ⟨v, a, b⟩ := hex e
      refine ⟨v, a, b, ?_⟩
      rw [(hpin f w s hs).1 h e v a b, h0]
      simp
    · rintro ⟨s, hs, hv⟩
      refine (hpin f w s hs).2 fun e v a b => ?_
      obtain ⟨v', a', b', c'⟩ := hv e
      obtain rfl := (TanLift.tangent_mod_torsion R T Γ S G x N i ht L M e).unique ⟨a, b⟩ ⟨a', b'⟩
      rw [c', h0]
      simp
  refine ⟨θ, ⟨hsurj, pin⟩, hker, ?_⟩
  rintro χ w ⟨s, hs, hv⟩
  have hχ : (fun t => ((χ t : Rˣ) : R)) ∈ Γ.btOrder ⊤ :=
    char_mem_hopfOrder R T _ (_root_.PositivityTheory.UnitarySelfGeneration.bt_hopf R T Γ) χ
  rw [OrderApi.dlogChar_of_mem _ χ hχ]
  refine (pin _ w).2 ⟨s - 1, fun t => ?_, fun e => ?_⟩
  · rw [valAt_sub_one, hs t]
    simp
  · obtain ⟨v, a, b, c⟩ := hv e
    refine ⟨v, a, b, ?_⟩
    rw [valAt_sub_one, c]
    refine TrivSqZeroExt.ext ?_ ?_ <;> simp

end GlobalTheory.CompanionTheory.Ar.BT
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FramedPointDescends
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

theorem GlobalTheory.CompanionTheory.Ar.Flat.exists_framed_residue : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (F : Type) [Field F] (β : c.F →+* F) (y : Sp F ⟶ Xo.XF c) (v : Vecs y D.p) (w : Vecs y D.q), IsFramed U τ β y v w → ∃ (k : Type) (_ : Field k) (β₀ : c.F →+* k) (y₀ : Sp k ⟶ Xo.XF c) (v₀ : Vecs y₀ D.p) (w₀ : Vecs y₀ D.q) (f : k →+* F) (j : k →+* ℂ), IsFramed U τ β₀ y₀ v₀ w₀ ∧ f.comp β₀ = β ∧ j.comp β₀ = algebraMap c.F ℂ ∧ y = spMap f ≫ y₀ ∧ ∀ (F' : Type) [Field F'] (f' : k →+* F'), ∃ (v' : Vecs (spMap f' ≫ y₀) D.p) (w' : Vecs (spMap f' ≫ y₀) D.q), IsFramed U τ (f'.comp β₀) (spMap f' ≫ y₀) v' w' ∧ (∀ a, (v' a).left = spMap (dualMap f') ≫ (v₀ a).left) ∧ ∀ b, (w' b).left = spMap (dualMap f') ≫ (w₀ b).left :=
  PositivityTheory.Xgn.framed_point_specialization
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateCokernelSharp
section
namespace GlobalTheory.CompanionTheory.Ar.HT

theorem hodge_tate_cokernel_sharp : GlobalTheory.CompanionTheory.Ar.HT.HodgeTateCokerSharp :=
  PositivityTheory.HtPt.Farsharp.hodgeTateCokerSharp

end GlobalTheory.CompanionTheory.Ar.HT
end

