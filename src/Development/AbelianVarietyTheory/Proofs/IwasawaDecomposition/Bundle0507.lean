module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0496
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFinsetOfMemNhds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0500
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0498
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0051

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSemiAbelianExponentialAlongDisc
section
noncomputable section

namespace GlobalTheory.RelExp

section General

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open Filter Topology GlobalTheory.TangentOrigin GlobalTheory.RelChart

private theorem etale_chart_lemma : ∀ (m g : ℕ) (A R : Type) [CommRing A] [CommRing R] (ψ : MvPolynomial (Fin g) A →+* R) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → (A →+* ℂ)) (b₀ : Fin m → ℂ) (e : R →+* ℂ), ψ.Etale → IsOpen B → b₀ ∈ B → (∀ a, DifferentiableOn ℂ (fun b => φ b a) B) → (∀ a, e (ψ (MvPolynomial.C a)) = φ b₀ a) → ∃ (N : Set ((Fin m → ℂ) × (Fin g → ℂ))) (σ : (Fin m → ℂ) × (Fin g → ℂ) → (R →+* ℂ)) (n : ℕ) (f : Fin n → R) (O : Set ((Fin m → ℂ) × (Fin n → ℂ))), IsOpen N ∧ IsOpen O ∧ (b₀, fun j => e (f j)) ∈ O ∧ (∀ a, DifferentiableOn ℂ (fun q => σ q a) N) ∧ (∀ q ∈ N, q.1 ∈ B ∧ (∀ a, σ q (ψ (MvPolynomial.C a)) = φ q.1 a) ∧ ∀ i, σ q (ψ (MvPolynomial.X i)) = q.2 i) ∧ ∀ (b : Fin m → ℂ) (x : R →+* ℂ), (∀ a, x (ψ (MvPolynomial.C a)) = φ b a) → (b, fun j => x (f j)) ∈ O → (b, fun i => x (ψ (MvPolynomial.X i))) ∈ N ∧ σ (b, fun i => x (ψ (MvPolynomial.X i))) = x := by
  exact fun m g A R _ _ ψ B φ b₀ e a a_1 a_2 a_3 a_4 =>
    EtaleFamily.exists_holomorphic_sections m g A R ψ B φ b₀ e a a_1 a_2 a_3 a_4

private theorem exists_open_smoothOfRelativeDimension : ∀ (Z X : Scheme.{0}) (p : Z ⟶ X) [Smooth p] (z : Z), ∃ (g : ℕ) (W : Z.Opens), z ∈ W ∧ SmoothOfRelativeDimension g (W.ι ≫ p) := by
  intro Z X p _ z
  exact H1.exists_dim p z

private theorem chart_lemma_4 : ∀ (m g : ℕ) (Z X : Scheme.{0}) (p : Z ⟶ X) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (b₀ : Fin m → ℂ) (z₀ : Sp ℂ ⟶ Z), SmoothOfRelativeDimension g p → IsOpen B → b₀ ∈ B → IsHolTo B y → z₀ ≫ p = y b₀ → ∃ (U : Z.Opens) (t : Fin g → Γ(Z, U)) (n : ℕ) (f : Fin n → Γ(Z, U)) (N : Set ((Fin m → ℂ) × (Fin g → ℂ))) (O : Set ((Fin m → ℂ) × (Fin n → ℂ))) (σ : (Fin m → ℂ) × (Fin g → ℂ) → (Sp ℂ ⟶ Z)), IsOpen N ∧ IsOpen O ∧ ⊤ ≤ z₀ ⁻¹ᵁ U ∧ (b₀, fun j => valAt' z₀ U (f j)) ∈ O ∧ IsHolTo N σ ∧ (∀ q ∈ N, σ q ≫ p = y q.1 ∧ ⊤ ≤ σ q ⁻¹ᵁ U ∧ ∀ i, valAt' (σ q) U (t i) = q.2 i) ∧ (∀ (b : Fin m → ℂ) (x : Sp ℂ ⟶ Z), x ≫ p = y b → ⊤ ≤ x ⁻¹ᵁ U → (b, fun j => valAt' x U (f j)) ∈ O → (b, fun i => valAt' x U (t i)) ∈ N ∧ σ (b, fun i => valAt' x U (t i)) = x) ∧ ∀ (v v' : Sp (DualNumber ℂ) ⟶ Z) (h : ⊤ ≤ v ⁻¹ᵁ U) (h' : ⊤ ≤ v' ⁻¹ᵁ U), v ≫ p = v' ≫ p → spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v' → (∀ i, GlobalTheory.TangentOrigin.evalPt v U h (t i) = GlobalTheory.TangentOrigin.evalPt v' U h' (t i)) → v = v' :=
  GlobalTheory.RelChart.exists_chart_with_parameters etale_chart_lemma

private theorem valAt'_presheaf_map_eqToHom {Y : Scheme.{0}} (x : Sp ℂ ⟶ Y) {V V' : Y.Opens} (h : V = V')
    (s : Γ(Y, V')) : valAt' x V ((Y.presheaf.map (eqToHom h).op).hom s) = valAt' x V' s := by
  subst h
  simp

private theorem evalPt_eqToHom {Y : Scheme.{0}} (v : Sp (DualNumber ℂ) ⟶ Y) {V V' : Y.Opens} (h : V = V')
    (hV : ⊤ ≤ v ⁻¹ᵁ V) (hV' : ⊤ ≤ v ⁻¹ᵁ V') (s : Γ(Y, V')) :
    GlobalTheory.TangentOrigin.evalPt v V hV ((Y.presheaf.map (eqToHom h).op).hom s) =
      GlobalTheory.TangentOrigin.evalPt v V' hV' s := by
  subst h
  simp

private theorem app_appIso_inv_eq_presheaf_map {Z : Scheme.{0}} (W : Z.Opens) (U' : (W : Scheme.{0}).Opens) (s : Γ(W, U')) :
    (W.ι.app (W.ι ''ᵁ U')).hom ((W.ι.appIso U').inv.hom s) =
      ((W : Scheme.{0}).presheaf.map (eqToHom (W.ι.preimage_image_eq U')).op).hom s := by
  rw [← Scheme.Hom.appIso_inv_app]
  rfl

private theorem valAt'_ι_appIso_inv {Z : Scheme.{0}} (W : Z.Opens) (U' : (W : Scheme.{0}).Opens) (x : Sp ℂ ⟶ W)
    (s : Γ(W, U')) : valAt' (x ≫ W.ι) (W.ι ''ᵁ U') ((W.ι.appIso U').inv.hom s) = valAt' x U' s := by
  rw [GlobalTheory.PointUnif.valAt'_comp, app_appIso_inv_eq_presheaf_map, valAt'_presheaf_map_eqToHom]

private theorem preimage_comp_ι_image_eq_preimage {Z : Scheme.{0}} (W : Z.Opens) (U' : (W : Scheme.{0}).Opens) {R : Type}
    [CommRing R] (x : Sp R ⟶ W) : (x ≫ W.ι) ⁻¹ᵁ (W.ι ''ᵁ U') = x ⁻¹ᵁ U' := by
  show x ⁻¹ᵁ (W.ι ⁻¹ᵁ (W.ι ''ᵁ U')) = x ⁻¹ᵁ U'
  rw [Scheme.Hom.preimage_image_eq]

private theorem evalPt_ι_appIso_inv {Z : Scheme.{0}} (W : Z.Opens) (U' : (W : Scheme.{0}).Opens)
    (v : Sp (DualNumber ℂ) ⟶ W) (h : ⊤ ≤ (v ≫ W.ι) ⁻¹ᵁ (W.ι ''ᵁ U')) (h' : ⊤ ≤ v ⁻¹ᵁ U') (s : Γ(W, U')) :
    GlobalTheory.TangentOrigin.evalPt (v ≫ W.ι) (W.ι ''ᵁ U') h ((W.ι.appIso U').inv.hom s) =
      GlobalTheory.TangentOrigin.evalPt v U' h' s := by
  rw [GlobalTheory.PointUnif.evalPt_comp, app_appIso_inv_eq_presheaf_map]
  exact evalPt_eqToHom v (W.ι.preimage_image_eq U') h h' s

private theorem exists_lift_through_opens_ι {Z : Scheme.{0}} (W : Z.Opens) (U' : (W : Scheme.{0}).Opens) {R : Type}
    [CommRing R] (x : Sp R ⟶ Z) (hx : ⊤ ≤ x ⁻¹ᵁ (W.ι ''ᵁ U')) : ∃ x' : Sp R ⟶ W, x' ≫ W.ι = x := by
  refine ⟨IsOpenImmersion.lift W.ι x ?_, IsOpenImmersion.lift_fac _ _ _⟩
  rintro _ ⟨a, rfl⟩
  obtain ⟨b, -, hb⟩ := hx (show a ∈ (⊤ : (Sp R).Opens) from trivial)
  exact ⟨b, hb⟩

theorem exists_chart_of_smooth (m : ℕ) (Z X : Scheme.{0}) (p : Z ⟶ X) (B : Set (Fin m → ℂ))
    (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (b₀ : Fin m → ℂ) (z₀ : Sp ℂ ⟶ Z) [Smooth p] (hB : IsOpen B) (hb₀ : b₀ ∈ B)
    (hy : IsHolTo B y) (hz₀ : z₀ ≫ p = y b₀) :
    ∃ (g : ℕ) (U : Z.Opens) (t : Fin g → Γ(Z, U)) (n : ℕ) (f : Fin n → Γ(Z, U)) (N : Set ((Fin m → ℂ) × (Fin g → ℂ))) (O : Set ((Fin m → ℂ) × (Fin n → ℂ))) (σ : (Fin m → ℂ) × (Fin g → ℂ) → (Sp ℂ ⟶ Z)), IsOpen N ∧ IsOpen O ∧ ⊤ ≤ z₀ ⁻¹ᵁ U ∧ (b₀, fun j => valAt' z₀ U (f j)) ∈ O ∧ IsHolTo N σ ∧ (∀ q ∈ N, σ q ≫ p = y q.1 ∧ ⊤ ≤ σ q ⁻¹ᵁ U ∧ ∀ i, valAt' (σ q) U (t i) = q.2 i) ∧ (∀ (b : Fin m → ℂ) (x : Sp ℂ ⟶ Z), x ≫ p = y b → ⊤ ≤ x ⁻¹ᵁ U → (b, fun j => valAt' x U (f j)) ∈ O → (b, fun i => valAt' x U (t i)) ∈ N ∧ σ (b, fun i => valAt' x U (t i)) = x) ∧ ∀ (v v' : Sp (DualNumber ℂ) ⟶ Z) (h : ⊤ ≤ v ⁻¹ᵁ U) (h' : ⊤ ≤ v' ⁻¹ᵁ U), v ≫ p = v' ≫ p → spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v' → (∀ i, GlobalTheory.TangentOrigin.evalPt v U h (t i) = GlobalTheory.TangentOrigin.evalPt v' U h' (t i)) → v = v' := by
  obtain ⟨g, W, hzW, hWsm⟩ := exists_open_smoothOfRelativeDimension Z X p (z₀.base default)
  have hz₀W : Set.range z₀.base ⊆ Set.range W.ι.base := by
    rintro _ ⟨a, rfl⟩
    rw [Subsingleton.elim a default, Scheme.Opens.range_ι]
    exact hzW
  obtain ⟨z₀', rfl⟩ : ∃ z₀' : Sp ℂ ⟶ W, z₀' ≫ W.ι = z₀ := ⟨_, IsOpenImmersion.lift_fac _ _ hz₀W⟩
  obtain ⟨U', t', n, f', N, O, σ', hN, hO, hU', hO', hσ', hσN', hinv', hun'⟩ :=
    chart_lemma_4 m g W X (W.ι ≫ p) B y b₀ z₀' hWsm hB hb₀ hy (by rw [← Category.assoc]; exact hz₀)
  refine ⟨g, W.ι ''ᵁ U', fun i => (W.ι.appIso U').inv.hom (t' i), n, fun j => (W.ι.appIso U').inv.hom (f' j), N, O,
    fun q => σ' q ≫ W.ι, hN, hO, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [preimage_comp_ι_image_eq_preimage]
    exact hU'
  · simp only [valAt'_ι_appIso_inv]
    exact hO'
  · exact isHolTo_of_holAt hN fun q hq => HolAt.post ⟨N, hN, hq, hσ'⟩ W.ι
  · intro q hq
    obtain ⟨h1, h2, h3⟩ := hσN' q hq
    refine ⟨by rw [Category.assoc]; exact h1, by rw [preimage_comp_ι_image_eq_preimage]; exact h2, fun i => ?_⟩
    rw [valAt'_ι_appIso_inv]
    exact h3 i
  · intro b x hxp hxU hxO
    obtain ⟨x', rfl⟩ := exists_lift_through_opens_ι W U' x hxU
    rw [preimage_comp_ι_image_eq_preimage] at hxU
    simp only [valAt'_ι_appIso_inv] at hxO ⊢
    obtain ⟨h1, h2⟩ := hinv' b x' (by rw [← Category.assoc]; exact hxp) hxU hxO
    exact ⟨h1, by rw [h2]⟩
  · intro v v' hv hv' hp h0 he
    obtain ⟨w, rfl⟩ := exists_lift_through_opens_ι W U' v hv
    obtain ⟨w', rfl⟩ := exists_lift_through_opens_ι W U' v' hv'
    have hw : ⊤ ≤ w ⁻¹ᵁ U' := by rw [← preimage_comp_ι_image_eq_preimage W U' w]; exact hv
    have hw' : ⊤ ≤ w' ⁻¹ᵁ U' := by rw [← preimage_comp_ι_image_eq_preimage W U' w']; exact hv'
    have hp' : w ≫ W.ι ≫ p = w' ≫ W.ι ≫ p := by simpa only [Category.assoc] using hp
    have h0' : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ w = spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ w' :=
      (cancel_mono W.ι).mp (by simpa only [Category.assoc] using h0)
    have he' : ∀ i, GlobalTheory.TangentOrigin.evalPt w U' hw (t' i) = GlobalTheory.TangentOrigin.evalPt w' U' hw' (t' i) := by
      intro i
      rw [← evalPt_ι_appIso_inv W U' w hv hw, ← evalPt_ι_appIso_inv W U' w' hv' hw']
      exact he i
    rw [hun' w w' hw hw' hp' h0' he']

theorem exists_relative_exp_of_smooth (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (m : ℕ)
    (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (b₀ : Fin m → ℂ) (hsm : Smooth G.hom)
    (hcon : GeometricallyConnected G.hom) (hB : IsOpen B) (hb₀ : b₀ ∈ B) (hy : IsHolTo B y) :
    ∃ (g : ℕ) (B' : Set (Fin m → ℂ)) (e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ G)), IsOpen B' ∧ b₀ ∈ B' ∧
      (∀ b ∈ B', (∀ z, HolAt (fun q : (Fin m → ℂ) × (Fin g → ℂ) => pt (e q.1 q.2)) (b, z)) ∧
        (∀ z w, (e b) (z + w) = (e b) z * (e b) w) ∧ Function.Surjective (e b) ∧
        IsHolTo Set.univ (fun z => pt ((e b) z)) ∧
        (∀ w, ∃! v : epsPt (y b) ⟶ G, IsDerivAt0 (fun z => ((e b) z).left) w v.left) ∧
        (∀ v : epsPt (y b) ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = ((e b) 0).left →
          ∃! w, IsDerivAt0 (fun z => ((e b) z).left) w v.left)) ∧
      ∀ z₀, e b₀ z₀ = 1 → ∃ ζ : (Fin m → ℂ) → (Fin g → ℂ), ζ b₀ = z₀ ∧ AnalyticAt ℂ ζ b₀ ∧
        ∀ᶠ b in 𝓝 b₀, e b (ζ b) = 1 := by
  haveI := hsm
  have hy' : HolAt y b₀ := ⟨B, hB, hb₀, hy⟩
  obtain ⟨g, U, t, n, f, N, O, σ, hN, hO, hU, hO₀, hσ, hσN, hinv, hun⟩ :=
    exists_chart_of_smooth m G.left X G.hom B y b₀ (1 : Over.mk (y b₀) ⟶ G).left hB hb₀ hy
      (Over.w (1 : Over.mk (y b₀) ⟶ G))
  obtain ⟨s, hs1, hs2, hs3⟩ := exists_centred_chart (G := G) (t := t) (f := f) hy' hN hU hO₀ hσ hσN hinv
  obtain ⟨B', e, r, Q, L, hB'o, hb₀', -, -, hQ, hadd, hprop, hinv'⟩ :=
    exists_global_exp (G := G) (t := t) (f := f) GlobalTheory.exists_param_exp_log_pi (hB.mem_nhds hb₀) hy' hO hU hO₀
      hs1 hs2 hs3
  refine ⟨g, B', e, hB'o, hb₀', fun b hb => ?_, fun z₀ hz₀ => ?_⟩
  · obtain ⟨hhol, hU1, hO1, hQ1, hder, -, -, -⟩ := hprop b hb
    have he0 : e b 0 = 1 := by
      have h := hadd b 0 0
      rw [add_zero] at h
      exact mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)
    have hhol' : IsHolTo Set.univ (fun z => pt (e b z)) :=
      isHolTo_of_holAt isOpen_univ fun z _ =>
        (hhol z).comp (φ := fun v : Fin g → ℂ => (b, v)) (analyticAt_const.prod analyticAt_id)
    obtain ⟨ht1, ht2⟩ := GlobalTheory.vertical_derivative_in_coordinates X G (y b) g (e b) hhol'
    have hU0 : ⊤ ≤ (show Sp ℂ ⟶ G.left from (e b 0).left) ⁻¹ᵁ U := by
      rw [he0]
      exact hU1
    have hfd : fderiv ℂ (fun z i => valAt' (e b z).left U (t i)) 0 = ContinuousLinearMap.id ℂ (Fin g → ℂ) :=
      hder.fderiv
    have hinj : Function.Injective (fderiv ℂ (fun z i => valAt' (e b z).left U (t i)) 0) := by
      rw [hfd]
      intro a a' h
      simpa using h
    let φ : Multiplicative (Fin g → ℂ) →* (Over.mk (y b) ⟶ G) :=
      { toFun := fun z => e b (Multiplicative.toAdd z)
        map_one' := he0
        map_mul' := fun z w => hadd b _ _ }
    have hH : φ.range = ⊤ := by
      refine GlobalTheory.OpenSubgroupPts.subgroup_eq_top_of_nhds_one X G (y b) φ.range U (Fin n ⊕ Fin g) (Sum.elim f t)
        {c | (b, fun j => c (Sum.inl j)) ∈ O ∧
          (b, (fun i => c (Sum.inr i)) - crd U t (pt (1 : Over.mk (y b) ⟶ G))) ∈ Q} hsm hcon ?_ hU1 ?_ ?_
      · exact (hO.preimage (by fun_prop)).inter (hQ.preimage (by fun_prop))
      · refine ⟨hO1, ?_⟩
        show (b, crd U t (pt (1 : Over.mk (y b) ⟶ G)) - crd U t (pt (1 : Over.mk (y b) ⟶ G))) ∈ Q
        rw [sub_self]
        exact hQ1
      · intro a ha1 ha2
        exact MonoidHom.mem_range.mpr ⟨Multiplicative.ofAdd (L (b, crd0 t a)), hinv' b a ha1 ha2.1 ha2.2⟩
    have hsurj : Function.Surjective (e b) := by
      intro a
      obtain ⟨z, hz⟩ := MonoidHom.mem_range.mp (hH ▸ Subgroup.mem_top a)
      exact ⟨Multiplicative.toAdd z, hz⟩
    exact ⟨hhol, hadd b, hsurj, hhol', ht1, (ht2 U t hU0 hun).mpr hinj⟩
  · obtain ⟨hhol, hU1, hO1, hQ1, -, hL0, hL, -⟩ := hprop b₀ hb₀'
    exact exists_lift (G := G) (y := y) (U := U) (t := t) (f := f) (O := O) (e := e) (Q := Q) (L := L)
      (β := fun w => w) (x := fun w => (1 : Over.mk (y w) ⟶ G)) (w₀ := b₀) (z₀ := z₀)
      hO hQ hadd hinv' analyticAt_id (HolAt.one hy') hz₀ (hhol z₀) hU1 hO1 hQ1 hL0 hL

end General

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
open scoped CategoryTheory.MonObj

theorem exists_exp_along_disc : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (y : ℂ → (Sp ℂ ⟶ X)) (r : ℝ), IsSemiAbelian G → 0 < r → IsHolTo (Metric.ball (0 : ℂ) r) y → ∃ (g : ℕ) (ρ : ℝ) (e : ∀ u, (Fin g → ℂ) → (Over.mk (y u) ⟶ G)), 0 < ρ ∧ ρ ≤ r ∧ IsHolTo (Metric.ball (0 : ℂ) ρ ×ˢ Set.univ) (fun q : ℂ × (Fin g → ℂ) => (show Sp ℂ ⟶ G.left from (e q.1 q.2).left)) ∧ (∀ u ∈ Metric.ball (0 : ℂ) ρ, (∀ z w, e u (z + w) = e u z * e u w) ∧ Function.Surjective (e u) ∧ IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ G.left from (e u z).left)) ∧ (∀ w, ∃! v : epsPt (y u) ⟶ G, IsDerivAt0 (fun z => (e u z).left) w v.left) ∧ (∀ v : epsPt (y u) ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e u 0).left → ∃! w, IsDerivAt0 (fun z => (e u z).left) w v.left)) ∧ ∀ z₀, e 0 z₀ = 1 → ∃ ζ : ℂ → (Fin g → ℂ), ζ 0 = z₀ ∧ AnalyticAt ℂ ζ 0 ∧ ∀ᶠ u in 𝓝 (0 : ℂ), e u (ζ u) = 1 := by
  intro X G _ y r hG hr hy
  haveI := hG.comm
  let c : ℂ → (Fin 1 → ℂ) := fun u _ => u
  have hcA : ∀ u, AnalyticAt ℂ c u := fun u =>
    (ContinuousLinearMap.pi fun _ : Fin 1 => ContinuousLinearMap.id ℂ ℂ).analyticAt u
  let y' : (Fin 1 → ℂ) → (Sp ℂ ⟶ X) := fun b => y (b 0)
  let B : Set (Fin 1 → ℂ) := (fun b : Fin 1 → ℂ => b 0) ⁻¹' Metric.ball 0 r
  have hBo : IsOpen B := Metric.isOpen_ball.preimage (continuous_apply 0)
  have hb0 : (0 : Fin 1 → ℂ) ∈ B := by
    show (0 : ℂ) ∈ Metric.ball (0 : ℂ) r
    exact Metric.mem_ball_self hr
  have hy' : IsHolTo B y' := isHolTo_of_holAt hBo fun b hb =>
    HolAt.comp (a := y) (φ := fun b : Fin 1 → ℂ => b 0) ⟨_, Metric.isOpen_ball, hb, hy⟩
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).analyticAt b)
  obtain ⟨g, B', e', hB'o, hb0', hprop, hfin⟩ :=
    exists_relative_exp_of_smooth X G 1 B y' 0 hG.smooth hG.geomConnected hBo hb0 hy'
  obtain ⟨ε, hε, hεB⟩ := Metric.isOpen_iff.mp hB'o 0 hb0'
  have hcB : ∀ u ∈ Metric.ball (0 : ℂ) (min ε r), c u ∈ B' := by
    intro u hu
    apply hεB
    rw [Metric.mem_ball, dist_zero_right]
    show ‖(fun _ : Fin 1 => u)‖ < ε
    rw [pi_norm_const]
    rw [Metric.mem_ball, dist_zero_right] at hu
    exact lt_of_lt_of_le hu (min_le_left _ _)
  refine ⟨g, min ε r, fun u => e' (c u), lt_min hε hr, min_le_right _ _, ?_, fun u hu => (hprop (c u) (hcB u hu)).2, ?_⟩
  · refine isHolTo_of_holAt (Metric.isOpen_ball.prod isOpen_univ) fun q hq => ?_
    exact ((hprop (c q.1) (hcB q.1 hq.1)).1 q.2).comp (φ := fun q : ℂ × (Fin g → ℂ) => (c q.1, q.2))
      (((ContinuousLinearMap.pi fun _ : Fin 1 => ContinuousLinearMap.fst ℂ ℂ (Fin g → ℂ)).prod
        (ContinuousLinearMap.snd ℂ ℂ (Fin g → ℂ))).analyticAt q)
  · intro z₀ hz₀
    obtain ⟨ζ, h1, h2, h3⟩ := hfin z₀ hz₀
    exact ⟨fun u => ζ (c u), h1, AnalyticAt.comp (f := c) (x := (0 : ℂ)) h2 (hcA 0), (hcA 0).continuousAt.tendsto.eventually h3⟩

end GlobalTheory.RelExp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniversalTripleFibreAtFramedPoint
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct

namespace GlobalTheory.KeyFourth

theorem card_frame_index {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : Datum H) {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) :
    Module.finrank ℚ E / 2 * (Dw.p + Dw.q) = g := by
  classical
  have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (E →+* ℂ)))
    (fun τ => τ (H.rt : E) = H.rt0)
  rw [Finset.card_univ, Embeddings.card] at h1
  have h2 := GlobalTheory.PeriodCoord.card_cmType H
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h2
  have h3 : Module.finrank ℚ E = 2 * Module.finrank ℚ (maximalRealSubfield E) := by
    rw [← (letI : Module.Free (maximalRealSubfield E) E := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E),
      Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E, mul_comm]
  have h4 : (Finset.univ.filter (fun τ : E →+* ℂ => ¬ τ (H.rt : E) = H.rt0)).card = Module.finrank ℚ E / 2 := by
    omega
  have h5 : (Finset.univ.filter (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0)).card = Module.finrank ℚ E / 2 := by
    omega
  have h6 := Fintype.card_congr e
  rw [Fintype.card_fin, Fintype.card_sigma] at h6
  simp_rw [Fintype.card_fin, Datum.mult] at h6
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, h4, h5, smul_eq_mul, smul_eq_mul] at h6
  rw [h6, mul_add]

theorem exists_tied : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (S : Type) [CommRing S] [Nontrivial S] [Algebra c.F S] (y : FrPt Xo c S), 1 ≤ Dw.p + Dw.q → ∃ Φ : FibKey Xo S y.x, Tied e y.s y.u Φ := by
  intro E _ _ _ H Dw l Xo c g e S _ _ _ y hpq
  obtain ⟨U, hU, hg⟩ := GlobalTheory.CM.exists_pat_of_obj E H Dw l _ _ _ _ Xo.univ
  obtain ⟨t, ⟨m⟩⟩ : ∃ t : SAB H (Sp S), Nonempty (SABMap t Xo.univ.t y.x) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull y.x Xo.univ.t
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨⟨T, rfl, hTg⟩, -⟩ := GlobalTheory.CM.PAT.exists_of_sabMap E H _ _ y.x U t (hU ▸ m)
  have hpos : 1 ≤ Module.finrank ℚ E / 2 := by
    have h1 := (letI : Module.Free (maximalRealSubfield E) E := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E)
    rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E] at h1
    have h2 : 0 < Module.finrank ℚ (maximalRealSubfield E) := Module.finrank_pos
    omega
  have hgp : 1 ≤ T.g := by
    rw [hTg, hg]
    exact Nat.mul_pos hpos hpq
  obtain rfl : T.g = g := hTg.trans (hg.trans (card_frame_index Dw e))
  obtain ⟨-, h₁, h₂⟩ := SecTieEx.secTie_exists_unique E H Dw l Xo S y.x T.t m
  obtain ⟨th, ht⟩ := h₁ y.s
  have hne := (h₂ th _ ht).2.1
    (GlobalTheory.Frames.secNZ_of_secGen GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo S _ _ y.gen)
  have hB := (GlobalTheory.Frames.eigBasis_iff_tanBasis E H Dw l Xo c S y.x y.u T.g e y.tan y.eig).1 y.basis
  obtain ⟨hl, hb⟩ := GlobalTheory.Frames.lieBasis_iff_tanBasis E H Dw l Xo S y.x T.t.G m.φ m.cart
  choose v hv using fun j => hl _ (y.tan (e j).1 (e j).2)
  refine ⟨⟨T, m, hgp, th, hne, v, (hb _ v).2 ?_⟩, ht, rfl, hv⟩
  rw [funext hv]
  exact hB

end GlobalTheory.KeyFourth

end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagRelativeTangentTopChernDvdOfDifferencesDvd
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

namespace GlobalTheory.GoodMetric.DiscrDvd

theorem irreducible_X_sub_X {σ : Type} {a b : σ} (h : a ≠ b) :
    Irreducible (X a - X b : MvPolynomial σ ℝ) := by
  classical
  have hc : AddMonoidAlgebra.coeff (X a - X b : MvPolynomial σ ℝ) (Finsupp.single a 1) = 1 := by
    have : ¬ (Finsupp.single b 1 = Finsupp.single a 1) := fun e =>
      h (Finsupp.single_left_injective one_ne_zero e).symm
    simp [coeff_X, this]
  refine irreducible_of_totalDegree_eq_one (le_antisymm ?_ ?_) fun x hx => ?_
  · exact (totalDegree_sub _ _).trans (by simp)
  · have := le_totalDegree (p := (X a - X b : MvPolynomial σ ℝ)) (s := Finsupp.single a 1)
      (by rw [mem_support_iff, hc]; exact one_ne_zero)
    simpa using this
  · exact isUnit_of_dvd_one (hc ▸ hx _)

theorem isRelPrime_X_sub_X {σ : Type} {a b c d : σ} (h : a ≠ b) (h' : c ≠ d)
    (hn : (c ≠ a ∧ c ≠ b) ∨ (d ≠ a ∧ d ≠ b)) :
    IsRelPrime (X a - X b : MvPolynomial σ ℝ) (X c - X d) := by
  classical
  refine (irreducible_X_sub_X h).isRelPrime_iff_not_dvd.2 fun hd => ?_
  rcases hn with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have := map_dvd (eval (Pi.single c (1 : ℝ))) hd
    simp [Pi.single_apply, h1.symm, h2.symm, h'.symm] at this
  · have := map_dvd (eval (Pi.single d (1 : ℝ))) hd
    simp [Pi.single_apply, h1.symm, h2.symm, h'] at this

theorem rootDiscr_dvd (ι : Type) [Fintype ι] (m : ι → ℕ) (P : MvPolynomial (Root m) ℝ)
    (hP : ∀ (τ : ι) (i j : Fin (m τ)), i < j → (X ⟨τ, j⟩ - X ⟨τ, i⟩ : MvPolynomial (Root m) ℝ) ∣ P) :
    GoodMetric.rootDiscr m ∣ P := by
  classical
  have ne : ∀ (τ : ι) (i j : Fin (m τ)), i ≠ j → (⟨τ, i⟩ : Root m) ≠ ⟨τ, j⟩ := fun τ i j h e =>
    h (eq_of_heq (Sigma.mk.inj e).2)
  unfold GoodMetric.rootDiscr
  refine Finset.prod_dvd_of_isRelPrime (fun τ _ τ' _ hτ => ?_) fun τ _ => ?_
  · refine IsRelPrime.prod_left fun j _ => IsRelPrime.prod_left fun i hi =>
      IsRelPrime.prod_right fun l _ => IsRelPrime.prod_right fun k hk => ?_
    refine isRelPrime_X_sub_X (ne _ _ _ (Finset.mem_Iio.1 hi).ne') (ne _ _ _ (Finset.mem_Iio.1 hk).ne')
      (Or.inl ⟨fun e => hτ (Sigma.mk.inj e).1.symm, fun e => hτ (Sigma.mk.inj e).1.symm⟩)
  refine Finset.prod_dvd_of_isRelPrime (fun j _ l _ hjl => ?_) fun j _ => ?_
  · refine IsRelPrime.prod_left fun i hi => IsRelPrime.prod_right fun k hk => ?_
    have hi := Finset.mem_Iio.1 hi
    have hk := Finset.mem_Iio.1 hk
    rcases lt_or_gt_of_ne hjl with h | h
    · exact isRelPrime_X_sub_X (ne _ _ _ hi.ne') (ne _ _ _ hk.ne')
        (Or.inl ⟨ne _ _ _ h.ne', ne _ _ _ (hi.trans h).ne'⟩)
    · exact (isRelPrime_X_sub_X (ne _ _ _ hk.ne') (ne _ _ _ hi.ne')
        (Or.inl ⟨ne _ _ _ h.ne', ne _ _ _ (hk.trans h).ne'⟩)).symm
  refine Finset.prod_dvd_of_isRelPrime (fun i hi k hk hik => ?_) fun i hi => hP τ i j (Finset.mem_Iio.1 hi)
  have hi := Finset.mem_Iio.1 hi
  have hk := Finset.mem_Iio.1 hk
  exact isRelPrime_X_sub_X (ne _ _ _ hi.ne') (ne _ _ _ hk.ne')
    (Or.inr ⟨ne _ _ _ hk.ne, ne _ _ _ hik.symm⟩)

end GlobalTheory.GoodMetric.DiscrDvd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagRelativeTangentTopChernRenameBlockPerm
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

namespace GlobalTheory.GoodMetric.RootDiscrPerm

theorem prod_Iio_eq_det {R : Type*} [CommRing R] {N : ℕ} (v : Fin N → R) :
    (∏ j : Fin N, ∏ i ∈ Finset.Iio j, (v j - v i)) = (Matrix.vandermonde v).det := by
  rw [Matrix.det_vandermonde]
  exact Finset.prod_comm' (fun j i => by simp [and_comm])

theorem det_vandermonde_comp_perm {R : Type*} [CommRing R] {N : ℕ} (v : Fin N → R) (σ : Equiv.Perm (Fin N)) :
    (Matrix.vandermonde (fun i => v (σ i))).det = ((Equiv.Perm.sign σ : ℤˣ) : ℤ) * (Matrix.vandermonde v).det := by
  have h : Matrix.vandermonde (fun i => v (σ i)) = (Matrix.vandermonde v).submatrix σ id := by
    ext i k; simp [Matrix.vandermonde_apply]
  rw [h, Matrix.det_permute]

theorem rootDiscr_eq_prod_det (ι : Type) [Fintype ι] (m : ι → ℕ) :
    rootDiscr m = ∏ τ, (Matrix.vandermonde (fun i : Fin (m τ) => (X ⟨τ, i⟩ : MvPolynomial (Root m) ℝ))).det := by
  unfold rootDiscr
  exact Finset.prod_congr rfl fun τ _ => prod_Iio_eq_det _

end GlobalTheory.GoodMetric.RootDiscrPerm

open GlobalTheory.GoodMetric.RootDiscrPerm in
theorem GlobalTheory.GoodMetric.rename_sigmaCongrRight_rootDiscr : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (w : ∀ τ, Equiv.Perm (Fin (m τ))), rename (Equiv.sigmaCongrRight w) (rootDiscr m) = ((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) • rootDiscr m := by
  intro ι _ m w
  rw [rootDiscr_eq_prod_det, map_prod]
  have h : ∀ τ, rename (Equiv.sigmaCongrRight w)
      (Matrix.vandermonde (fun i : Fin (m τ) => (X ⟨τ, i⟩ : MvPolynomial (Root m) ℝ))).det =
      ((Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) * (Matrix.vandermonde (fun i : Fin (m τ) => (X ⟨τ, i⟩ : MvPolynomial (Root m) ℝ))).det := by
    intro τ
    rw [AlgHom.map_det]
    have e : (rename (Equiv.sigmaCongrRight w) : MvPolynomial (Root m) ℝ →ₐ[ℝ] MvPolynomial (Root m) ℝ).mapMatrix
        (Matrix.vandermonde (fun i : Fin (m τ) => (X ⟨τ, i⟩ : MvPolynomial (Root m) ℝ))) =
        Matrix.vandermonde (fun i : Fin (m τ) => (X ⟨τ, w τ i⟩ : MvPolynomial (Root m) ℝ)) := by
      ext i k; simp [Matrix.vandermonde_apply]
    rw [e]
    exact det_vandermonde_comp_perm (fun i : Fin (m τ) => (X ⟨τ, i⟩ : MvPolynomial (Root m) ℝ)) (w τ)
  rw [Finset.prod_congr rfl fun τ _ => h τ, Finset.prod_mul_distrib, zsmul_eq_mul]
  push_cast
  rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceDimensionEqSumChoose
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle

namespace GlobalTheory.FlagDimSum

theorem mul_add_choose_two (p q : ℕ) :
    p * q + p.choose 2 + q.choose 2 = (p + q).choose 2 := by
  induction q with
  | zero => simp
  | succ q ih =>
    have h1 : (q + 1).choose 2 = q + q.choose 2 := by
      rw [Nat.choose_succ_succ' q 1, Nat.choose_one_right]
    have h2 : (p + q + 1).choose 2 = (p + q) + (p + q).choose 2 := by
      rw [Nat.choose_succ_succ' (p + q) 1, Nat.choose_one_right]
    rw [← add_assoc, h1, h2, ← ih]
    ring

theorem dim_add_sum_choose : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H), Dw.dim + ∑ τ : E →+* ℂ, (Dw.mult τ).choose 2 =
      Module.finrank ℚ E / 2 * ((Dw.p + Dw.q) * (Dw.p + Dw.q - 1) / 2) := by
  intro E _ _ _ H Dw
  classical
  have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (E →+* ℂ)))
    (fun τ => τ (H.rt : E) = H.rt0)
  rw [Finset.card_univ, Embeddings.card] at h1
  have h2 := GlobalTheory.PeriodCoord.card_cmType H
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h2
  have h3 : Module.finrank ℚ E = 2 * Module.finrank ℚ (maximalRealSubfield E) := by
    rw [← (letI : Module.Free (maximalRealSubfield E) E := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E),
      Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E, mul_comm]
  have h4 : (Finset.univ.filter (fun τ : E →+* ℂ => ¬ τ (H.rt : E) = H.rt0)).card =
      Module.finrank ℚ E / 2 := by
    omega
  have hs : ∑ τ : E →+* ℂ, (Dw.mult τ).choose 2 =
      Module.finrank ℚ E / 2 * (Dw.p.choose 2 + Dw.q.choose 2) := by
    simp_rw [Datum.mult, apply_ite (fun n : ℕ => n.choose 2)]
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, h4, h2, smul_eq_mul, smul_eq_mul, mul_add]
  rw [hs, Datum.dim, ← Nat.choose_two_right, ← mul_add_choose_two, mul_assoc, ← mul_add, ← add_assoc]

end GlobalTheory.FlagDimSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralCharts
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.LN GlobalTheory.TorRef GlobalTheory.IntegralCombination GlobalTheory.UU Formalism.L2.Pj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.IntFam

def IntegralCharts {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R)
    (J : (Spec (CommRingCat.of (FractionRing R)) ⟶ D.P.A.left) → D.P.L.ι) : Prop :=
  ∀ p : Spec (CommRingCat.of R) ⟶ D.P.A.left, p ≫ D.P.A.hom = 𝟙 _ →
    p (closedPoint R) ∈ D.P.L.U (J (jK R ≫ p))

end GlobalTheory.IntFam
end
end

