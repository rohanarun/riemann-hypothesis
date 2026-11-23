module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0544
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FrameMatrixHasSum
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLaw
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0525
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0548
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalBoundaryMetricData
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0537
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartWiden
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0434

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CombSnd
section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.ArcLieCoord

attribute [local instance] Over.cartesianMonoidalCategory

open MonoidalCategory CartesianMonoidalCategory MonObj Filter GlobalTheory.ArcLie

section Group

variable {S : Type} [CommRing S] {X : Scheme.{0}} {x : Sp S ⟶ X} {G : Over X} {G' : Over (Sp S)} [GrpObj G]
  [GrpObj G'] {φ : G'.left ⟶ G.left}

theorem tan_le (h : IsGrpPullback G' G x φ) (w : epsR S ⟶ G') (hw : IsTangent w) (V : G.left.Opens)
    (hV : ⊤ ≤ ((η[G']).left ≫ φ) ⁻¹ᵁ V) : ⊤ ≤ (w.left ≫ φ) ⁻¹ᵁ V := by
  unfold IsTangent at hw
  rw [GlobalTheory.ArcLie.le_iff_fst, ← Category.assoc, hw]
  exact hV

theorem comb_snd [IsCommMonObj G'] (h : IsGrpPullback G' G x φ) {n : ℕ} (v : Fin n → (epsR S ⟶ G'))
    (hv : ∀ k, IsTangent (v k)) (c : Fin n → S) (w : epsR S ⟶ G') (hc : IsLieComb c v w) (V : G.left.Opens)
    (hV : ⊤ ≤ ((η[G']).left ≫ φ) ⁻¹ᵁ V) (f : Γ(G.left, V)) :
    (valR (w.left ≫ φ) V f).snd = ∑ k, c k * (valR ((v k).left ≫ φ) V f).snd := by
  obtain ⟨u, hu, hp⟩ := (ReciprocityTheory.ChartRestriction.G.Chart.comb_push h c v w).1 hc
  have e1 : (show Sp S ⟶ G'.left from (1 : Over.mk (𝟙 (Sp S)) ⟶ G').left) = (η[G']).left := by
    have : (1 : Over.mk (𝟙 (Sp S)) ⟶ G') = η[G'] := by
      rfl
    rw [this]
  have key := GlobalTheory.ArcLie.snd_comb_lift h (x' := 𝟙 (Sp S)) (Category.id_comp x) (fun k => (v k).left)
    (fun k => by rw [Category.comp_id]; exact Over.w (v k)) (fun k => (ReciprocityTheory.ChartRestriction.G.Chart.tan_push h (v k)).1 (hv k))
    c w.left (by rw [Category.comp_id]; exact Over.w w) u hu hp (φ ⁻¹ᵁ V) (by rw [e1]; exact hV) ((φ.app V).hom f)
  rw [GlobalTheory.HolHom.valR_comp, key]
  exact Finset.sum_congr rfl fun k _ => by rw [GlobalTheory.HolHom.valR_comp]

end Group

end GlobalTheory.ArcLieCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompleteHolomorphicCoordinatesIndependentDiffere
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section

namespace GlobalTheory.CompleteCoords

theorem exists_linearIndependent_extend {M : Type*} [AddCommGroup M] [Module ℂ M]
    [FiniteDimensional ℂ M] {a : ℕ} (ℓ : Fin a → M) (hℓ : LinearIndependent ℂ ℓ) :
    ∀ m : ℕ, a + m ≤ Module.finrank ℂ M → ∃ f : Fin (a + m) → M, LinearIndependent ℂ f ∧
      ∀ i : Fin a, f (Fin.castAdd m i) = ℓ i := by
  intro m
  induction m with
  | zero => intro _; exact ⟨ℓ, hℓ, fun i => rfl⟩
  | succ m ih =>
    intro h
    obtain ⟨f, hf, hfℓ⟩ := ih (by omega)
    obtain ⟨x, hx⟩ := exists_linearIndependent_snoc_of_lt_finrank hf (by omega)
    refine ⟨Fin.snoc f x, hx, fun i => ?_⟩
    have e : (Fin.castAdd (m + 1) i : Fin (a + (m + 1))) = Fin.castSucc (Fin.castAdd m i) := rfl
    rw [e, Fin.snoc_castSucc, hfℓ]

theorem complete_coords : ∀ (n a : ℕ) (v₀ : ReciprocityTheory.L2DbarEstimates.V n) (O : Set (ReciprocityTheory.L2DbarEstimates.V n)) (G : Fin a → ReciprocityTheory.L2DbarEstimates.V n → ℂ), IsOpen O → v₀ ∈ O → (∀ i, DifferentiableOn ℂ (G i) O) → (∀ i, G i v₀ = 0) → LinearIndependent ℂ (fun i => fderiv ℂ (G i) v₀) → ∃ ψ : OpenPartialHomeomorph (ReciprocityTheory.L2DbarEstimates.V n) (Fin n → ℂ), v₀ ∈ ψ.source ∧ ψ.source ⊆ O ∧ ψ v₀ = 0 ∧ DifferentiableOn ℂ ψ ψ.source ∧ DifferentiableOn ℂ ψ.symm ψ.target ∧ ∀ v ∈ ψ.source, ∀ (j : Fin n) (hj : (j : ℕ) < a), ψ v j = G ⟨j, hj⟩ v := by
  intro n a v₀ O G hO hv₀ hG hG0 hli
  classical
  set ℓ : Fin a → (ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] ℂ) := fun i => fderiv ℂ (G i) v₀ with hℓdef
  have hfr : Module.finrank ℂ (ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] ℂ) = n := by
    rw [← LinearEquiv.finrank_eq (LinearMap.toContinuousLinearMap), Module.finrank_linearMap,
      finrank_euclideanSpace_fin, Module.finrank_self, Nat.mul_one]
  have han : a ≤ n := by
    have := hli.fintype_card_le_finrank
    simpa [hfr] using this
  obtain ⟨f', hf', hf'ℓ⟩ := exists_linearIndependent_extend ℓ hli (n - a) (by rw [hfr]; omega)
  have hn : a + (n - a) = n := by omega
  set f : Fin n → (ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] ℂ) := fun j => f' (Fin.cast hn.symm j) with hfdef
  have hf : LinearIndependent ℂ f := hf'.comp _ (Fin.cast_injective _)
  have hfa : ∀ (j : Fin n) (h : (j : ℕ) < a), f j = ℓ ⟨j, h⟩ := by
    intro j h
    have e : Fin.cast hn.symm j = Fin.castAdd (n - a) ⟨j, h⟩ := Fin.ext rfl
    simp only [hfdef, e, hf'ℓ]

  set Φ : ReciprocityTheory.L2DbarEstimates.V n → (Fin n → ℂ) :=
    fun v j => if h : (j : ℕ) < a then G ⟨j, h⟩ v else f j (v - v₀) with hΦ
  have hGan : ∀ i, ∀ x ∈ O, AnalyticAt ℂ (G i) x := fun i x hx =>
    ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA.analyticAt_of_diffOn hO (hG i) hx
  have hΦan : ∀ x ∈ O, AnalyticAt ℂ Φ x := by
    intro x hx
    refine (analyticAt_pi_iff (f := fun j v => Φ v j)).2 fun j => ?_
    by_cases h : (j : ℕ) < a
    · simpa [hΦ, h] using hGan ⟨j, h⟩ x hx
    · simp only [hΦ, h, dite_false]
      exact ((f j).analyticAt _).comp (analyticAt_id.sub analyticAt_const)

  set D : ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] (Fin n → ℂ) := ContinuousLinearMap.pi f with hD
  have hΦD : HasFDerivAt Φ D v₀ := by
    refine (hasFDerivAt_pi (φ := fun j v => Φ v j)).2 fun j => ?_
    by_cases h : (j : ℕ) < a
    · simp only [hΦ, h, dite_true]
      rw [hfa j h]
      exact ((hGan ⟨j, h⟩ v₀ hv₀).differentiableAt).hasFDerivAt
    · simp only [hΦ, h, dite_false]
      have e : (fun x => f j (x - v₀)) = fun x => f j x - f j v₀ := by
        funext x; simp [map_sub]
      rw [e]
      exact (f j).hasFDerivAt.sub_const _
  have hinj : Function.Injective D := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro v hv
    have hv' : ∀ j, f j v = 0 := fun j => by
      have := congrFun hv j
      simpa [hD] using this
    have hspan : Submodule.span ℂ (Set.range f) = ⊤ := by
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0
        exact Subsingleton.elim _ _
      · haveI : Nonempty (Fin n) := ⟨⟨0, hpos⟩⟩
        exact hf.span_eq_top_of_card_eq_finrank (by simp [hfr])
    have hall : ∀ φ : ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] ℂ, φ v = 0 := by
      intro φ
      have hmem : φ ∈ Submodule.span ℂ (Set.range f) := hspan ▸ Submodule.mem_top
      refine Submodule.span_induction (p := fun φ _ => φ v = 0) ?_ ?_ ?_ ?_ hmem
      · rintro _ ⟨j, rfl⟩; exact hv' j
      · simp
      · intro x y _ _ hx hy; simp [hx, hy]
      · intro c x _ hx; simp [hx]
    by_contra hne
    obtain ⟨φ, hφ⟩ := SeparatingDual.exists_ne_zero (R := ℂ) hne
    exact hφ (hall φ)
  have hsurj : Function.Surjective D := by
    have := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := (D : ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] (Fin n → ℂ)))
      (by simp [finrank_euclideanSpace_fin])).1 hinj
    exact this
  set e : ReciprocityTheory.L2DbarEstimates.V n ≃L[ℂ] (Fin n → ℂ) := ContinuousLinearEquiv.ofBijective D
    (LinearMap.ker_eq_bot.2 hinj) (LinearMap.range_eq_top.2 hsurj) with he
  have heD : (e : ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] (Fin n → ℂ)) = D := by
    rw [he, ContinuousLinearEquiv.coe_ofBijective]
  have hs : HasStrictFDerivAt Φ (e : ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] (Fin n → ℂ)) v₀ := by
    have h1 := ((hΦan v₀ hv₀).contDiffAt (n := 1)).hasStrictFDerivAt_fderiv one_ne_zero
    rwa [hΦD.fderiv, ← heD] at h1

  have hΦC : ContDiffOn ℂ 1 Φ O := AnalyticOnNhd.contDiffOn (fun x hx => hΦan x hx) hO.uniqueDiffOn
  set W : Set (ReciprocityTheory.L2DbarEstimates.V n) :=
    O ∩ fderiv ℂ Φ ⁻¹' Set.range ContinuousLinearEquiv.toContinuousLinearMap with hW
  have hWo : IsOpen W :=
    (hΦC.continuousOn_fderiv_of_isOpen hO le_rfl).isOpen_inter_preimage hO
      ContinuousLinearEquiv.isOpen
  have hv₀W : v₀ ∈ W := ⟨hv₀, ⟨e, by rw [hΦD.fderiv, heD]⟩⟩
  refine ⟨(hs.toOpenPartialHomeomorph Φ).restrOpen W hWo, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [OpenPartialHomeomorph.restrOpen_source]
    exact ⟨hs.mem_toOpenPartialHomeomorph_source, hv₀W⟩
  · rw [OpenPartialHomeomorph.restrOpen_source]
    exact fun x hx => hx.2.1
  · show Φ v₀ = 0
    funext j
    by_cases h : (j : ℕ) < a
    · simp [hΦ, h, hG0]
    · simp [hΦ, h]
  · intro x hx
    rw [OpenPartialHomeomorph.restrOpen_source] at hx
    exact (hΦan x hx.2.1).differentiableAt.differentiableWithinAt
  · intro y hy
    set ψ := (hs.toOpenPartialHomeomorph Φ).restrOpen W hWo with hψ
    have hx : ψ.symm y ∈ ψ.source := ψ.map_target hy
    rw [hψ, OpenPartialHomeomorph.restrOpen_source] at hx
    obtain ⟨e', he'⟩ := hx.2.2
    have hd : HasFDerivAt (ψ : ReciprocityTheory.L2DbarEstimates.V n → (Fin n → ℂ))
        (e' : ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] (Fin n → ℂ)) (ψ.symm y) := by
      have := (hΦan _ hx.2.1).differentiableAt.hasFDerivAt
      rw [← he'] at this
      exact this
    exact (ψ.hasFDerivAt_symm hy hd).differentiableAt.differentiableWithinAt
  · intro v _ j hj
    show Φ v j = _
    simp [hΦ, hj]

end GlobalTheory.CompleteCoords
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexPointMemClosedIffFactorVanishes
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam

theorem mem_iff_exists_ev_eq_zero_of_ideal_eq_span_prod : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (σ : k →+* ℂ) (D : TopologicalSpace.Closeds Y) (U : Y.affineOpens) (m : ℕ) (f : Fin m → Γ(Y, U.1)) (J : Finset (Fin m)), (Scheme.IdealSheafData.vanishingIdeal D).ideal U = Ideal.span {∏ i ∈ J, f i} → ∀ x : CxPts p σ, x ∈ CxPts.ptsIn p σ U.1 → (x.1 (IsLocalRing.closedPoint ℂ) ∈ D ↔ ∃ i ∈ J, CxPts.ev p σ U.1 (f i) x = 0) := by
  intro k _ Y p σ D U m f J h x hx
  have h1 := (ev_eq_zero_iff h hx).symm
  rw [LiesIn] at h1
  rw [h1, CxPts.ev_eq hx, map_prod, Finset.prod_eq_zero_iff]
  simp only [CxPts.ev_eq hx]

end GlobalTheory.ShFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CubicalWeilPairingTorsionConstHolomorphicFamily
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionPairFam


open HolTorsion in
theorem cubWeil_const_of_isHolTo : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (L : ReciprocityTheory.ChartRestriction.G.Semi.RigLB G) (c : ReciprocityTheory.ChartRestriction.G.Semi.CubicalStr G L) (m N : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (x x' : ∀ b, Over.mk (y b) ⟶ G) (ζ : ℂˣ) (b₀ b₁ : Fin m → ℂ), 0 < N → IsOpen B → IsPreconnected B → IsHolTo B (fun b => (x b).left) → IsHolTo B (fun b => (x' b).left) → (∀ b ∈ B, x b ^ N = 1 ∧ x' b ^ N = 1) → b₀ ∈ B → b₁ ∈ B → GlobalTheory.UU.CubWeil c N (x b₀) (x' b₀) (unitOn ζ) → GlobalTheory.UU.CubWeil c N (x b₁) (x' b₁) (unitOn ζ) := by
  intro X G _ _ L c m N B y x x' ζ b₀ b₁ hN _ hB hx hx' htor hb₀ hb₁ h₀
  let o : X ⟶ G.left := (η[G] : 𝟙_ (Over X) ⟶ G).left
  have ho : o ≫ G.hom = 𝟙 X := Over.w (η[G] : 𝟙_ (Over X) ⟶ G)
  let mk : G ⟶ G := (𝟙 G) ^ N
  have hkill : ∀ (T : Over X) (u : T ⟶ G), u ^ N = 1 ↔ u.left ≫ mk.left = T.hom ≫ o := by
    intro T u
    have e₁ : u.left ≫ mk.left = (u ^ N).left := by
      rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
    have e₂ : T.hom ≫ o = (1 : T ⟶ G).left := by
      rw [Hom.one_def, Over.comp_left, Over.toUnit_left]
    rw [e₁, e₂]
    exact ⟨fun h => by rw [h], fun h => Over.OverMorphism.ext h⟩
  let p := pullback.fst mk.left o
  let q := pullback.snd mk.left o
  have H : IsPullback p q mk.left o := IsPullback.of_hasPullback _ _
  have hpq : p ≫ G.hom = q := by
    rw [← Over.w mk, ← Category.assoc, H.w, Category.assoc, ho, Category.comp_id]
  have hy : IsHolTo B y := isHolTo_congr (isHolTo_comp hx G.hom) fun b _ => (Over.w (x b)).symm
  obtain ⟨a, ha, hab⟩ := exists_isHolTo_lift H hx hy (fun b hb => (hkill _ _).1 (htor b hb).1) hb₀
  obtain ⟨a', ha', hab'⟩ := exists_isHolTo_lift H hx' hy (fun b hb => (hkill _ _).1 (htor b hb).2) hb₀
  obtain ⟨z, hz, hzb⟩ := exists_isHolTo_lift (IsPullback.of_hasPullback q q) ha ha'
    (fun b hb => (hab b hb).2.trans (hab' b hb).2.symm) hb₀
  let T : Over X := Over.mk (pullback.fst q q ≫ q)
  let u : T ⟶ G := Over.homMk (pullback.fst q q ≫ p) (by
    show (pullback.fst q q ≫ p) ≫ G.hom = pullback.fst q q ≫ q
    rw [Category.assoc, hpq])
  let v : T ⟶ G := Over.homMk (pullback.snd q q ≫ p) (by
    show (pullback.snd q q ≫ p) ≫ G.hom = pullback.fst q q ≫ q
    rw [Category.assoc, hpq, pullback.condition])
  have hu : u ^ N = 1 := (hkill T u).2 (by
    show (pullback.fst q q ≫ p) ≫ _ = (pullback.fst q q ≫ q) ≫ o
    rw [Category.assoc, H.w, Category.assoc])
  have hv : v ^ N = 1 := (hkill T v).2 (by
    show (pullback.snd q q ≫ p) ≫ _ = (pullback.fst q q ≫ q) ≫ o
    rw [Category.assoc, H.w, pullback.condition, Category.assoc])
  obtain ⟨e, he, -⟩ := UU.existsUnique_cubWeil c hu hv
  have hek : e.val ^ N = 1 := congrArg Units.val he.pow_eq_one
  have hpull : ∀ w ∈ B, UU.CubWeil c N (x w) (x' w) (Units.map (z w).appTop.hom.toMonoidHom e) := by
    intro w hw
    let h : Over.mk (y w) ⟶ T := Over.homMk (z w) (by
      show z w ≫ pullback.fst q q ≫ q = y w
      rw [← Category.assoc, (hzb w hw).1, (hab w hw).2])
    have e₁ : h ≫ u = x w := Over.OverMorphism.ext (by
      show z w ≫ pullback.fst q q ≫ p = _
      rw [← Category.assoc, (hzb w hw).1, (hab w hw).1])
    have e₂ : h ≫ v = x' w := Over.OverMorphism.ext (by
      show z w ≫ pullback.snd q q ≫ p = _
      rw [← Category.assoc, (hzb w hw).2, (hab' w hw).1])
    have := he.comp h
    rw [e₁, e₂] at this
    exact this
  have e₀ : Units.map (z b₀).appTop.hom.toMonoidHom e = unitOn ζ := (hpull b₀ hb₀).unique h₀
  have e₁ : Units.map (z b₁).appTop.hom.toMonoidHom e = Units.map (z b₀).appTop.hom.toMonoidHom e :=
    Units.ext ((val_map_appTop (z b₁) e.val).trans
      ((congrArg _ (valAt'_eq_of_pow_eq_one hz hB hN hek hb₀ hb₁)).trans (val_map_appTop (z b₀) e.val).symm))
  have := hpull b₁ hb₁
  rw [e₁, e₀] at this
  exact this

end GlobalTheory.TorsionPairFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetNeZeroOfImHermFormIntegralRealBasis
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory


open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory.Limits _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped Matrix CategoryTheory.Obj Topology in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.det_ne_zero_of_im_hermForm_eq_int : ∀ (g r : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (lam : Fin r → Fin g → ℂ) (M : Matrix (Fin r) (Fin r) ℤ), (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm u u).re) → LinearIndependent ℝ lam → Submodule.span ℝ (Set.range lam) = ⊤ → (∀ i j, (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (lam i) (lam j)).im = M i j) → M.det ≠ 0 := by
  intro g r Hm lam M hpos hli hspan hM hdet
  have hdet' : (M.map (Int.cast : ℤ → ℝ)).det = 0 := by
    have h := RingHom.map_det (Int.castRingHom ℝ) M
    rw [hdet, map_zero] at h
    exact h.symm
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet'
  set w : Fin g → ℂ := ∑ j, v j • lam j with hwdef
  have hw0 : w ≠ 0 := by
    intro hw
    apply hv0
    funext j
    exact Fintype.linearIndependent_iff.mp hli v hw j
  have hlin : ∀ x : Fin g → ℂ, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm x w = ∑ j, v j • _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm x (lam j) := by
    intro x
    simp only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, hwdef, star_sum, star_smul, star_trivial, Matrix.mulVec_sum,
      Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul]
  have hlamw : ∀ i, (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (lam i) w).im = 0 := by
    intro i
    have hrow := congrFun hv i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply] at hrow
    rw [hlin, Complex.im_sum]
    simp only [Complex.smul_im, hM, smul_eq_mul]
    rw [← hrow]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hall : ∀ x, (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm x w).im = 0 := by
    intro x
    have hx : x ∈ Submodule.span ℝ (Set.range lam) := hspan ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact hlamw i
    | zero => simp [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm]
    | add y z _ _ hy hz =>
      simp only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, add_dotProduct, Complex.add_im] at hy hz ⊢
      rw [hy, hz, add_zero]
    | smul c y _ hy =>
      simp only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, smul_dotProduct, Complex.smul_im] at hy ⊢
      rw [hy, smul_zero]
  have hI := hall (Complex.I • w)
  have hre := hpos w hw0
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, smul_dotProduct, smul_eq_mul, Complex.mul_im, Complex.I_re,
    Complex.I_im, zero_mul, one_mul, zero_add] at hI hre
  linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetNeZeroOfRealIndependentIsotropicHermitian
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem det_ne_zero_of_real_indep_isotropic : ∀ (g : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (E : Fin g → Fin g → ℂ), (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) → LinearIndependent ℝ E → (∀ i j, (hermForm Hm (E i) (E j)).im = 0) → (Matrix.of fun k i => E i k).det ≠ 0 := by
  intro g Hm E hpos hind him
  have hL : ∀ (a : Fin g → ℝ) (w : Fin g → ℂ), hermForm Hm (∑ i, (a i : ℂ) • E i) w
      = ∑ i, (a i : ℂ) * hermForm Hm (E i) w := by
    intro a w
    simp only [hermForm, sum_dotProduct, smul_dotProduct, smul_eq_mul]
  have hR : ∀ (b : Fin g → ℝ) (z : Fin g → ℂ), hermForm Hm z (∑ j, (b j : ℂ) • E j)
      = ∑ j, (b j : ℂ) * hermForm Hm z (E j) := by
    intro b z
    have hs : star (∑ j, (b j : ℂ) • E j) = ∑ j, (b j : ℂ) • star (E j) := by
      rw [star_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ext k
      simp
    simp only [hermForm, hs, Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul, smul_eq_mul]
  have him0 : ∀ a b : Fin g → ℝ,
      (hermForm Hm (∑ i, (a i : ℂ) • E i) (∑ j, (b j : ℂ) • E j)).im = 0 := by
    intro a b
    rw [hL]
    simp only [hR, Finset.mul_sum, Complex.im_sum]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    simp [Complex.mul_im, him i j]
  have hsmulL : ∀ (c : ℂ) (z w : Fin g → ℂ), hermForm Hm (c • z) w = c * hermForm Hm z w := by
    intro c z w
    simp only [hermForm, smul_dotProduct, smul_eq_mul]
  have hreal : ∀ a : Fin g → ℝ, (∑ i, (a i : ℂ) • E i) = 0 → a = 0 := by
    intro a h0
    have h1 : ∑ i, a i • E i = 0 := by
      rw [← h0]
      refine Finset.sum_congr rfl fun i _ => ?_
      ext k
      simp
    have := Fintype.linearIndependent_iff.mp hind a h1
    funext i
    exact this i
  have hC : LinearIndependent ℂ E := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hsplit : (∑ i, (((c i).re : ℝ) : ℂ) • E i) + Complex.I • (∑ i, (((c i).im : ℝ) : ℂ) • E i) = 0 := by
      rw [← hc, Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, ← add_smul]
      congr 1
      exact (mul_comm Complex.I _ ▸ Complex.re_add_im (c i))
    set X := ∑ i, (((c i).re : ℝ) : ℂ) • E i with hX
    set Y := ∑ i, (((c i).im : ℝ) : ℂ) • E i with hY
    have hXY : X = (-Complex.I) • Y := by
      rw [neg_smul]
      exact eq_neg_of_add_eq_zero_left hsplit
    have hY0 : Y = 0 := by
      by_contra hne
      have hp := hpos Y hne
      have h2 := him0 (fun i => (c i).re) (fun i => (c i).im)
      change (hermForm Hm X Y).im = 0 at h2
      rw [hXY, hsmulL] at h2
      simp [Complex.mul_im] at h2
      linarith
    have hX0 : X = 0 := by rw [hXY, hY0, smul_zero]
    have hre := hreal (fun i => (c i).re) hX0
    have him' := hreal (fun i => (c i).im) hY0
    intro i
    apply Complex.ext
    · simpa using congrFun hre i
    · simpa using congrFun him' i
  have hcol : LinearIndependent ℂ (Matrix.of fun k i => E i k : Matrix (Fin g) (Fin g) ℂ).col := hC
  have hu := Matrix.linearIndependent_cols_iff_isUnit.mp hcol
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharacterAllChartsFurtherPlacesStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_character_allCharts_furtherPlaces : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Ch0 : B.Word → ℕ → Type) (chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (h1 : 1 ≤ B.R.m - 1) (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) (g : Ch → Ch0 u (B.R.m - 1)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u)) → (∀ u j v h, (F u).glevJ.fr j v h = 1) → (∃ k : Ch → GA B (B.R.N (B.R.m - 1)), I.Reads u a (B.R.m - 1) chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧ ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1) → (∀ β, GlobalTheory.Mem.Col2.AdT.ChiFin I l Z (K β).lev) → (∀ β, ∀ v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) → (∀ β (κ : (K β).lev.U) (κ' : ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.chi κ') → ∀ (Lb0 : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin ((I.rec7 l Z).sp.X (B.R.m - 1)).rank → (I.rec7 l Z).host.E)), (F u).levJ.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) Lb0 → ∃ ψ : (∀ v : Q, ↥(⨆ β', ((K β').lev.Uloc v.1).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom)) →* ℂˣ, ∀ β (κ : (K β).lev.U) (z : ∀ v : Q, ↥(⨆ β', ((K β').lev.Uloc v.1).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom)), (∀ v : Q, reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ (z v).1 = bc (prV (E := (I.rec7 l Z).host.E) v.1) κ.1) → (∀ v, v ∉ Q → bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ψ z := by
  first | exact @GlobalTheory.Mem.Col2.QChi.exists_chi_further | exact GlobalTheory.Mem.Col2.QChi.exists_chi_further | (intros; apply GlobalTheory.Mem.Col2.QChi.exists_chi_further <;> assumption)
end

