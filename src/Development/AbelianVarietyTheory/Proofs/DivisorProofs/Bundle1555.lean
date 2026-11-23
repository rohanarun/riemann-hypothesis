module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1523
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0055
public import Formalism.LocalToGlobal.Divisibility.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0802
public import Formalism.LocalToGlobal.Divisibility.HeckeCSDICommTrRep
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1527
public import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1520

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramedPointCoordinatesMemSpanEigenLattice
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames
open ReciprocityTheory.ChartRestriction.G

noncomputable section

namespace GlobalTheory.PtDeg.FrameEig

theorem dualMapR_epsScaleR {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (a : R) :
    spMap (Chart.dualMapR f) ≫ spMap (epsScaleR a) = spMap (epsMul (f a)) ≫ spMap (Chart.dualMapR f) := by
  rw [GlobalTheory.IntLie.spMap_comp₂, GlobalTheory.IntLie.spMap_comp₂]
  congr 1
  apply RingHom.ext
  intro r
  ext <;> simp [epsMul, epsScaleR, Chart.dualMapR, mul_comm]

theorem epsScaleR_epsMul_comm {R : Type} [CommRing R] (a b : R) :
    spMap (epsScaleR a) ≫ spMap (epsMul b) = spMap (epsMul b) ≫ spMap (epsScaleR a) := by
  rw [GlobalTheory.IntLie.spMap_comp₂, GlobalTheory.IntLie.spMap_comp₂]
  congr 1
  apply RingHom.ext
  intro r
  ext <;> simp [epsMul, epsScaleR, mul_left_comm]

theorem scale_eig {R : Type} [CommRing R] {X : Scheme.{0}} (a b : R) (x : Sp (DualNumber R) ⟶ X) (g : X ⟶ X)
    (h : x ≫ g = spMap (epsMul b) ≫ x) :
    (spMap (epsScaleR a) ≫ x) ≫ g = spMap (epsMul b) ≫ spMap (epsScaleR a) ≫ x := by
  rw [Category.assoc, h, ← Category.assoc, epsScaleR_epsMul_comm, Category.assoc]

theorem epsScaleR_eq_epsMul {R : Type} [CommRing R] (a : R) : epsScaleR a = epsMul a := rfl

theorem sc_left {R : Type} [CommRing R] {G : Over (Sp R)} (a : R) (v : epsR R ⟶ G) :
    (GlobalTheory.CM.IntCoord.sc a ≫ v).left = spMap (epsScaleR a) ≫ v.left := rfl

end GlobalTheory.PtDeg.FrameEig


open GlobalTheory.PtDeg.FrameEig in
theorem GlobalTheory.PtDeg.frameCoord_mem_span_eigLat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (ρ : E →+* ℂ) (tt : 𝓞 E →+* 𝓞 K), (∀ a, ((tt a : 𝓞 K) : K) = algebraMap c.F K (embK c ρ a)) → ∀ (u : Fin (Dw.mult ρ) → Fin F.P₀.g → K), GlobalTheory.PtDeg.FrameCoord y m1 m2 F ρ u → ∀ j, u j ∈ Submodule.span K (F.eigLat B.t.act tt : Set (Fin F.P₀.g → K)) := by
  intro E _ _ _ H Dw l Xo c K _ _ _ y B t₀ m1 m2 F ρ tt htt u hu j
  obtain ⟨u₀, w, h₁, h₂, hc⟩ := hu j
  have h₂' : u₀ ≫ m2.cm.F = w.left ≫ F.φ := h₂
  have h₁' : u₀ ≫ m1.cm.F = y.u ρ j := h₁

  have hbase : u₀ ≫ t₀.G.hom = spMap (algebraMap K (DualNumber K)) := by
    apply GlobalTheory.IntLie.spMap_frac_cancel (V := 𝓞 K)
    rw [Category.assoc, ← m2.cart.1.w, ← Category.assoc, h₂', Category.assoc]
    have e := F.fib.2.1.1.w
    erw [e]
    rw [← Category.assoc, Over.w w]
    rfl

  have hact0 : ∀ a : 𝓞 E, u₀ ≫ (t₀.act.act a).left = spMap (epsMul ((tt a : 𝓞 K) : K)) ≫ u₀ := by
    intro a
    apply m1.cart.1.hom_ext
    · rw [Category.assoc, m1.act a, ← Category.assoc, h₁', y.eig ρ j a, htt a, Category.assoc, h₁']
    · rw [Category.assoc, Over.w (t₀.act.act a), hbase, Category.assoc, hbase, GlobalTheory.IntLie.spMap_comp₂,
        GlobalTheory.IntLie.epsMul_alg]

  have hw : ∀ a : 𝓞 E, w.left ≫ F.φ ≫ (B.t.act.act a).left =
      spMap (epsMul ((tt a : 𝓞 K) : K)) ≫ w.left ≫ F.φ := by
    intro a
    rw [← reassoc_of% h₂', ← m2.act a, ← Category.assoc, hact0, Category.assoc, h₂']

  have hc' : u j ∈ Submodule.span K (F.lieLat : Set (Fin F.P₀.g → K)) := by
    rw [(GlobalTheory.CM.LieLattice.lieLat_fg_and_span_eq_top K B.pol F).2]; trivial
  obtain ⟨d, hd⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 K)) K _ (u j) hc'
  rw [Submodule.span_eq, Submonoid.smul_def] at hd
  obtain ⟨-, -, -, -, hlat, heig⟩ := GlobalTheory.CM.integral_tangent_coordinates K B.pol F
  obtain ⟨U, hUt, w₁, hUv, hw₁⟩ := (hlat _).1 hd
  have := F.P₀.isAb.comm
  have hK := GlobalTheory.LieComb.lieComb_algebra K F.P₀.A _ F.v F.basis.1
  set dK : K := algebraMap (𝓞 K) K (d : 𝓞 K) with hdK
  have hw₁' : w₁ = GlobalTheory.CM.IntCoord.sc dK ≫ w := by
    have h3 := hK.2.2.1 1 ![u j] ![w] ![dK] _ (fun i => by fin_cases i; exact hc)
      ((GlobalTheory.CM.IntCoord.isLieComb_one_iff _ _ _).2 rfl)
    simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Matrix.cons_val_fin_one,
      Finset.sum_singleton] at h3
    rw [← algebraMap_smul K (d : 𝓞 K) (u j)] at hw₁
    exact (hK.1 _).unique hw₁ h3
  have hw₁e : ∀ a : 𝓞 E, w₁.left ≫ F.φ ≫ (B.t.act.act a).left =
      spMap (epsMul ((tt a : 𝓞 K) : K)) ≫ w₁.left ≫ F.φ := by
    intro a
    rw [hw₁', sc_left, Category.assoc, Category.assoc]
    have := scale_eig dK ((tt a : 𝓞 K) : K) (w.left ≫ F.φ) (B.t.act.act a).left (by rw [Category.assoc, hw a])
    simpa only [Category.assoc] using this

  have := B.pol.isAb.proper
  have hmem : (d : 𝓞 K) • u j ∈ F.eigLat B.t.act tt := by
    rw [heig]
    refine ⟨U, ⟨hUt, w₁, hUv, hw₁⟩, fun a => ?_⟩
    rw [GlobalTheory.CM.IntCoord.isLieComb_one_iff]
    have hv1 : IsVecOver (algebraMap (𝓞 K) K) F.φ (U ≫ B.t.act.act a)
        (GlobalTheory.CM.IntCoord.sc ((tt a : 𝓞 K) : K) ≫ w₁) := by
      unfold IsVecOver at hUv ⊢
      rw [sc_left, Over.comp_left, ← Category.assoc, ← hUv, Category.assoc, Category.assoc, hw₁e a,
        epsScaleR_eq_epsMul]
    have hv2 : IsVecOver (algebraMap (𝓞 K) K) F.φ (GlobalTheory.CM.IntCoord.sc (tt a) ≫ U)
        (GlobalTheory.CM.IntCoord.sc ((tt a : 𝓞 K) : K) ≫ w₁) := by
      unfold IsVecOver at hUv ⊢
      rw [sc_left, sc_left, Category.assoc, hUv, epsScaleR_eq_epsMul]
      have e := dualMapR_epsScaleR (algebraMap (𝓞 K) K) (tt a)
      exact ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ U.left) e).trans (Category.assoc _ _ _))).symm
    exact GlobalTheory.CM.IntCoord.eq_of_isVecOver (IsFractionRing.injective (𝓞 K) K) hv1 hv2

  have hd0 : dK ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 (nonZeroDivisors.coe_ne_zero d)
  have h₃ := Submodule.smul_mem (Submodule.span K (F.eigLat B.t.act tt : Set (Fin F.P₀.g → K))) dK⁻¹
    (Submodule.subset_span hmem)
  rwa [← algebraMap_smul K (d : 𝓞 K) (u j), ← hdK, inv_smul_smul₀ hd0] at h₃
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramedPointGenericFibreCoordinatesEqFrame
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames

namespace GlobalTheory.PtDeg.FrameGen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem over_of_fib {K : Type} [Field K] [NumberField K] {B : GlobalTheory.CM.PAT H (Sp (𝓞 K))} {t₀ : SAB H (Sp K)}
    (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol)
    (u₀ : Sp (DualNumber K) ⟶ t₀.G.left) (w : epsR K ⟶ F.P₀.A) (h : u₀ ≫ m2.φ = w.left ≫ F.φ) :
    u₀ ≫ t₀.G.hom = spMap (algebraMap K (DualNumber K)) := by
  haveI : Epi (CommRingCat.ofHom (algebraMap (𝓞 K) K)) := IsLocalization.epi (nonZeroDivisors (𝓞 K)) K
  haveI : Mono (spMap (algebraMap (𝓞 K) K)) := Scheme.Spec.map_mono (CommRingCat.ofHom _).op
  rw [← cancel_mono (spMap (algebraMap (𝓞 K) K)), Category.assoc, ← m2.cart.1.w, ← Category.assoc, h,
    Category.assoc]
  have := F.fib.2.1.1.w
  erw [this, ← Category.assoc, Over.w w]
  rfl

end GlobalTheory.PtDeg.FrameGen

namespace GlobalTheory.PtDeg.FrameGen

theorem spMap_dualMap_algebraMap {S R : Type} [CommRing S] [CommRing R] (f : S →+* R) :
    spMap (dualMap f) ≫ spMap (algebraMap S (DualNumber S)) = spMap (algebraMap R (DualNumber R)) ≫ spMap f := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x
  · simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  · simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem spMap_dualMap_id {S : Type} [CommRing S] : spMap (dualMap (RingHom.id S)) = 𝟙 _ := by
  have : dualMap (RingHom.id S) = RingHom.id _ := by
    apply RingHom.ext
    intro x
    apply TrivSqZeroExt.ext <;> simp [dualMap]
  simp only [spMap, this]
  exact Spec.map_id _

end GlobalTheory.PtDeg.FrameGen

namespace GlobalTheory.PtDeg.FrameGen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem exists_lift_eps {K Tf : Type} [CommRing K] [CommRing Tf] {G' : Over (Sp Tf)} {G : Over (Sp K)}
    (f : K →+* Tf) {φ : G'.left ⟶ G.left} (hp : IsPullback φ G'.hom G.hom (spMap f))
    (u₀ : Sp (DualNumber K) ⟶ G.left) (hu : u₀ ≫ G.hom = spMap (algebraMap K (DualNumber K))) :
    ∃ g : epsR Tf ⟶ G', g.left ≫ φ = spMap (dualMap f) ≫ u₀ :=
  ⟨Over.homMk (hp.lift (spMap (dualMap f) ≫ u₀) (spMap (algebraMap Tf (DualNumber Tf)))
      (by rw [Category.assoc, hu, spMap_dualMap_algebraMap])) (hp.lift_snd _ _ _), hp.lift_fst _ _ _⟩

theorem isLieComb_of_match {K : Type} [Field K] [NumberField K] {B : GlobalTheory.CM.PAT H (Sp (𝓞 K))} {t₀ : SAB H (Sp K)}
    (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) {T : CDVR} (iK : K →+* T.Fr)
    {t' : SAB H (Sp T.Fr)} (n' : SABMap t' t₀ (spMap iK)) {v' : Fin F.P₀.g → (epsR T.Fr ⟶ t'.G)}
    (hv' : IsLieBasis v')
    (hv'φ : ∀ k, (v' k).left ≫ n'.φ ≫ m2.φ = spMap (dualMap iK) ≫ (F.v k).left ≫ F.φ)
    (c : Fin F.P₀.g → K) (w : epsR K ⟶ F.P₀.A) (hw : IsLieComb c F.v w) (g : epsR T.Fr ⟶ t'.G)
    (hg : g.left ≫ n'.φ ≫ m2.φ = spMap (dualMap iK) ≫ w.left ≫ F.φ) :
    IsLieComb (fun k => iK (c k)) v' g := by
  obtain ⟨w', hw'⟩ := ((GlobalTheory.LieComb.lieComb_algebra T.Fr t'.G _ v' hv'.1).1 (fun k => iK (c k))).exists
  have hpb := IsGrpPullback.comp n'.cart m2.cart
  have hid : spMap (RingHom.id T.Fr) = 𝟙 _ := by
    simp only [spMap, CommRingCat.ofHom_id]
    exact Spec.map_id _
  have key := GlobalTheory.LamT.LetterInt.comb_match hpb F.fib.2.1 (RingHom.id T.Fr) iK
    (by rw [hid, Category.id_comp]) (v₁ := v') (v₂ := F.v)
    (fun k => by rw [spMap_dualMap_id, Category.id_comp]; exact hv'φ k) (c₁ := fun k => iK (c k)) (c₂ := c)
    (fun k => rfl) hw' hw
  rw [spMap_dualMap_id, Category.id_comp, ← hg] at key
  have : w' = g := Over.OverMorphism.ext (hpb.1.hom_ext key (by rw [Over.w w', Over.w g]))
  subst this
  exact hw'

end GlobalTheory.PtDeg.FrameGen

namespace GlobalTheory.PtDeg.FrameGen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem comb_left_of_isCombAt {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {Tf : Type} [CommRing Tf]
    {x : Sp Tf ⟶ Xo.X} {t' : SAB H (Sp Tf)} (m1' : SABMap t' Xo.univ.t x) {m : ℕ}
    (e : Fin m → (Sp (DualNumber Tf) ⟶ Xo.univ.t.G.left)) (cc : Fin m → Tf)
    (z : Sp (DualNumber Tf) ⟶ Xo.univ.t.G.left) (hz : IsCombAt x e cc z) (g : Fin m → (epsR Tf ⟶ t'.G))
    (hg : ∀ j, (g j).left ≫ m1'.φ = e j) (w'' : epsR Tf ⟶ t'.G) (hw : IsLieComb cc g w'') :
    w''.left ≫ m1'.φ = z := by
  obtain ⟨b, hb, rfl⟩ := hz
  obtain ⟨a, ha, rfl⟩ := hw
  have := GlobalTheory.LamT.LetterInt.prod_pull m1'.cart (epsR Tf) _ (𝟙 _) (by rw [Category.id_comp]; rfl) a b
    (fun j => by rw [hb j, Category.id_comp, ha j, Category.assoc, hg j]; rfl)
  rw [this, Category.id_comp]

end GlobalTheory.PtDeg.FrameGen

namespace GlobalTheory.PtDeg

open GlobalTheory.PtDeg.FrameGen in
theorem frame_genFib_coords : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (ρ : E →+* ℂ) (u : Fin (Dw.mult ρ) → Fin F.P₀.g → K), GlobalTheory.PtDeg.FrameCoord y m1 m2 F ρ u → ∀ (T : CDVR) (iK : K →+* T.Fr), letI := (iK.comp (algebraMap c.F K)).toAlgebra; ∀ (yT : FrPt Xo c T.Fr), FrMap ({ iK with commutes' := fun _ => rfl } : K →ₐ[c.F] T.Fr) y yT → ∀ (t' : SAB H (Sp T.Fr)) (n' : SABMap t' t₀ (spMap iK)) (m1' : SABMap t' Xo.univ.t yT.x), m1'.φ = n'.φ ≫ m1.φ → ∀ (v' : Fin F.P₀.g → (epsR T.Fr ⟶ t'.G)), IsLieBasis v' → (∀ k, (v' k).left ≫ n'.φ ≫ m2.φ = spMap (Formalism.L2.Pj.dualMap iK) ≫ (F.v k).left ≫ F.φ) → ∀ (C : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) T.Fr) (a : T.Fr) (y' : FrPt Xo c T.Fr), FrChg C a yT y' → ∀ (i : Fin (Dw.mult ρ)) (u'' : Sp (DualNumber T.Fr) ⟶ t'.G.left), u'' ≫ t'.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) → u'' ≫ m1'.φ = y'.u ρ i → ∃ w'' : epsR T.Fr ⟶ t'.G, w''.left = u'' ∧ IsLieComb (∑ j, C ρ i j • fun k => iK (u j k)) v' w'' := by
  intro E _ _ _ H Dw l Xo c K _ _ _ y B t₀ m1 m2 F ρ u hF T iK
  letI : Algebra c.F T.Fr := (iK.comp (algebraMap c.F K)).toAlgebra
  intro yT hyT t' n' m1' h1 v' hv' hv'φ C a y' hchg i u'' hu''0 hu''1
  choose u₀ w hu₁ hu₂ hw using hF
  have hover : ∀ j, u₀ j ≫ t₀.G.hom = spMap (algebraMap K (DualNumber K)) :=
    fun j => over_of_fib m2 F (u₀ j) (w j) (hu₂ j)
  choose g hg using fun j => exists_lift_eps iK n'.cart.1 (u₀ j) (hover j)
  have hg1 : ∀ j, (g j).left ≫ m1'.φ = yT.u ρ j := fun j => by
    rw [h1, ← Category.assoc, hg j, Category.assoc, hu₁ j]
    exact (hyT.2.1 ρ j).symm
  have hcomb : ∀ j, IsLieComb (fun k => iK (u j k)) v' (g j) := fun j =>
    isLieComb_of_match m2 F iK n' hv' hv'φ (u j) (w j) (hw j) (g j)
      (by rw [← Category.assoc, hg j, Category.assoc, hu₂ j])
  have hA := GlobalTheory.LieComb.lieComb_algebra T.Fr t'.G _ v' hv'.1
  have htan : ∀ j, IsTangent (g j) := fun j => hA.2.1 _ _ (hcomb j)
  have hB := GlobalTheory.LieComb.lieComb_algebra T.Fr t'.G _ g htan
  obtain ⟨w'', hw''⟩ := (hB.1 (C ρ i)).exists
  have hleft : w''.left ≫ m1'.φ = y'.u ρ i :=
    comb_left_of_isCombAt m1' (yT.u ρ) (C ρ i) _ (hchg.2.1 ρ i) g hg1 w'' hw''
  refine ⟨w'', m1'.cart.1.hom_ext (by rw [hleft, hu''1]) (by rw [Over.w w'', hu''0]; rfl), ?_⟩
  exact hA.2.2.1 _ (fun j k => iK (u j k)) g (C ρ i) w'' hcomb hw''

end GlobalTheory.PtDeg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesTildeGammaValues
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows GlobalTheory.ColRows
open scoped ComplexOrder

namespace GlobalTheory.ColEvNorm

open _root_.Formalism.L2.Col in
theorem rowCast_injective {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)
    {SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (e : Pr.vGs = SG') (A : LevFam X.E X.K (R.N R.m - 1) Pr.vGs)
    (Λ' : LevFam X.E X.K (R.N R.m - 1) SG') (hΛ : Λ' = e ▸ A) :
    Function.Injective (rowCast W e A Λ' hΛ) := by
  subst hΛ
  subst e
  intro F G h
  exact h

open _root_.Formalism.L2.Col in
theorem zOfRow_injective {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Formalism.L2.DIV.Tup X.F X.E X.K S)
    (hQ : QE sel (mu : Formalism.L2.DIV.Chr X.F X.E X.K) = ∅) (P : LevFam X.E X.K R.r Pr.vGs) (σ₀ : X.K →+* ℂ)
    (hM : (rowGSD W (rowTyG Ch P).inv).Ok) :
    Function.Injective (zOfRow W Ch sel mu hQ P σ₀ hM) := by
  intro F G h
  apply rowCast_injective W (rcol_rowSG_eq sel mu hQ) (rowTyG Ch P).inv _ (rowTy_inv_cast Ch sel mu hQ P)
  apply ((rowGSD W (rowTyG Ch P).inv).hB hM).repr.injective
  ext a
  exact σ₀.injective (congrFun h a)

end GlobalTheory.ColEvNorm

namespace GlobalTheory.ColEvNorm


open _root_.Formalism.L2.Col in
theorem ipAt_le_of_ties {Xf : Fields} [_root_.NumberField.IsTotallyComplex Xf.K]
    (Pr : Primes Xf) (Rk : Ranks) (W : Wts Xf Pr.Word Rk) (Ch : Chars Xf Pr Rk.m)
    (sel : HeightOneSpectrum (𝓞 Xf.F) → HeightOneSpectrum (𝓞 Xf.E)) {Sg : Set ℕ} (hX : Xf.Ok)
    (Lv : LevFam Xf.E Xf.K Rk.r Pr.vGs) (Xg : Finset (G0 Xf.E Pr.vGs Rk.r → Xf.K)) (v0 : InfinitePlace Xf.K)
    (TU : Finset (Formalism.L2.DIV.Tup Xf.F Xf.E Xf.K Sg))
    (xiVal : Formalism.L2.DIV.Tup Xf.F Xf.E Xf.K Sg → HeightOneSpectrum (𝓞 Xf.E) → Xf.Kˣ)
    (trIv : Fin Rk.m → (LevOffI ∅ Pr.vGs ∅ × List ℕ → Xf.K) → LevOffI ∅ Pr.vGs ∅ × List ℕ → Xf.K)
    {Gp : Type} [grp : Group Gp] [fin : Fintype Gp] {Pl0 I0 Tt : Type} {m : ℕ}
    (A3 : FamIn3 Xf.K Gp Pl0 I0 (List ℕ) Tt m) (Ps : Subgroup Gp) (ψs : Ps →* Xf.Kˣ) (Zs : DefSub A3.fam3.amb3)
    (mu : A3.fam3.base3.Tup → Formalism.L2.DIV.Tup Xf.F Xf.E Xf.K Sg) (hP : ∀ t, (mtildeGSD W Ch sel (mu t) Lv).Ok)
    (gEq : Gp = G0 Xf.E Pr.vGs Rk.r) (hgrp : HEq grp (Pi.group : Group (G0 Xf.E Pr.vGs Rk.r)))
    (hm3 : Rk.m = m) (plEq : Pl0 = LevOff ∅ Pr.vGs ∅) (i0Eq : I0 = LevOffI ∅ Pr.vGs ∅) (tEq : Tt = TupF TU)
    (famEq : HEq A3 (colIn3 W Ch sel hX v0 TU Xg ∅ xiVal trIv))
    (muTie : ∀ t, mu t = (cast tEq t).1) (ok1 : A3.fam3.Ok3 1)
    (hps1 : HEq Ps Lv.grp) (hps2 : HEq ψs Lv.chr)
    (X0 : InfinitePlace Xf.K → Matrix (Fin ((A3.side3 Ps ψs Zs).nV A3.fam3.base3.μ0))
      (Fin ((A3.side3 Ps ψs Zs).nV A3.fam3.base3.μ0)) ℂ)
    (hX0 : GlobalTheory.ColRows.IsFrames (A3.side3 Ps ψs Zs) X0) (v : InfinitePlace Xf.K)
    (F : Fin ((A3.side3 Ps ψs Zs).nV A3.fam3.base3.μ0) → Xf.K)
    (F' : (mtildeKGSD W Ch sel (mu A3.fam3.base3.μ0)).EqFun)
    (hm : F'.1 ∈ (mtildeGSD W Ch sel (mu A3.fam3.base3.μ0) Lv).EqFun)
    (hres : HEq ((mtildeKGSD W Ch sel (mu A3.fam3.base3.μ0)).res (mtildeKOk W Ch sel (mu A3.fam3.base3.μ0) hX) F')
      ((A3.A.fam.R A3.fam3.base3.μ0).S.basis.equivFun.symm
        (((A3.A.fam.R A3.fam3.base3.μ0).S.cutE (A3.A.fam.R A3.fam3.base3.μ0).r
          (lvlIdem (A3.A.fam.lvl Ps ψs).P (A3.A.fam.lvl Ps ψs).ψ)).mulVec
          (((A3.A.fam.R A3.fam3.base3.μ0).S.lvlPr (A3.A.fam.R A3.fam3.base3.μ0).r (A3.A.fam.lvl Ps ψs).P
            (A3.A.fam.lvl Ps ψs).ψ * (A3.A.fam.R A3.fam3.base3.μ0).vE (A3.A.fam.lvl Ps ψs)).mulVec F)))) :
    ((mtildeGSD W Ch sel (mu A3.fam3.base3.μ0) Lv).ipAt (hP A3.fam3.base3.μ0) v F'.1 F'.1).re ≤
      Formalism.HermitianLatticesTheory.normAt (Pi.basisFun Xf.K (Fin ((A3.side3 Ps ψs Zs).nV A3.fam3.base3.μ0))) X0 v F ^ 2 := by
  subst gEq
  have hg : grp = (Pi.group : Group (G0 Xf.E Pr.vGs Rk.r)) := eq_of_heq hgrp
  subst hg
  run_tac do
    let g ← Lean.Elab.Tactic.getMainGoal
    let g' ← g.withContext do
      let lctx ← Lean.getLCtx
      let some fe := lctx.findFromUserName? `famEq | throwError "famEq"
      let some fi := lctx.findFromUserName? `fin | throwError "fin"
      let t ← Lean.instantiateMVars fe.type
      let ty ← Lean.Meta.whnf (← Lean.Meta.inferType t.appArg!)
      let inst := ty.getAppArgs[6]!
      let pf ← Lean.Meta.mkAppM ``Subsingleton.elim #[fi.toExpr, inst]
      let (_, g') ← g.note `hfin pf
      pure g'
    Lean.Elab.Tactic.replaceMainGoal [g']
  subst hfin
  subst hm3
  subst plEq
  subst i0Eq
  subst tEq
  have hA := eq_of_heq famEq
  subst hA
  have hp1 := eq_of_heq hps1
  subst hp1
  have hp2 := eq_of_heq hps2
  subst hp2
  have hmuE : mu = fun t => t.1 := funext muTie
  subst hmuE
  exact _root_.GlobalTheory.ClassSumLevel.classSum_le_normAt_sq Xf Pr Rk W Ch sel Sg hX v0 TU Xg ∅ xiVal trIv Lv Zs _ (hP _) ok1 F F' hm hres v X0
    (hX0 v).1 (hX0 v).2

end GlobalTheory.ColEvNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasHermitianSignatureHyperbolicPlaneOrthCompleme
section
open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PlaneSkew

noncomputable section

namespace GlobalTheory.PlaneSkewSig

open Matrix

theorem conjTranspose_eq_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : Mᴴ = M := by
  obtain ⟨hn, A, hA⟩ := h
  set D : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ := Matrix.fromBlocks 1 0 0 (-1) with hD
  have hDD : D * D = 1 := by
    simp [hD, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
  have hDh : Dᴴ = D := by
    simp [hD, Matrix.fromBlocks_conjTranspose]
  have hAh : Aᵀ * Mᴴ * A.map star = D := by
    have a1 : (A.map star)ᴴ = Aᵀ := by ext; simp [conjTranspose_apply]
    have a2 : (Aᵀ)ᴴ = A.map star := by ext; simp [conjTranspose_apply]
    have : (Aᵀ * M * A.map star)ᴴ = Aᵀ * Mᴴ * A.map star := by
      rw [conjTranspose_mul, conjTranspose_mul, a1, a2, Matrix.mul_assoc]
    rw [← this, hA, hDh]
  have e : Fin r ⊕ Fin s ≃ Fin n := (finSumFinEquiv).trans (finCongr hn)
  have k1 : M * (A.map star * D * Aᵀ) = 1 := by
    have : Aᵀ * (M * A.map star * D) = 1 := by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hA, hDD]
    have := (Matrix.mul_eq_one_comm_of_equiv e).1 this
    simpa [Matrix.mul_assoc] using this
  have k2 : Mᴴ * (A.map star * D * Aᵀ) = 1 := by
    have : Aᵀ * (Mᴴ * A.map star * D) = 1 := by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hAh, hDD]
    have := (Matrix.mul_eq_one_comm_of_equiv e).1 this
    simpa [Matrix.mul_assoc] using this
  have k3 : (A.map star * D * Aᵀ) * M = 1 := mul_eq_one_comm.1 k1
  calc Mᴴ = Mᴴ * ((A.map star * D * Aᵀ) * M) := by rw [k3, Matrix.mul_one]
    _ = M := by rw [← Matrix.mul_assoc, k2, Matrix.one_mul]

theorem exists_left_inverse {m k : ℕ} (ι : Matrix (Fin m) (Fin k) ℂ) (h : Function.Injective ι.mulVec) :
    ∃ P : Matrix (Fin k) (Fin m) ℂ, P * ι = 1 := by
  have hker : LinearMap.ker (Matrix.mulVecLin ι) = ⊥ := LinearMap.ker_eq_bot.2 h
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hker
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have := congrArg LinearMap.toMatrix' hg
  rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id] at this
  have e : LinearMap.toMatrix' ι.mulVecLin = ι := LinearMap.toMatrix'_toLin' ι
  rwa [e] at this

theorem transpose_mulVec_eq_zero {m k : ℕ} (ι : Matrix (Fin m) (Fin k) ℂ) (v : Fin m → ℂ)
    (h : ∀ u, (ι *ᵥ u) ⬝ᵥ v = 0) : ιᵀ *ᵥ v = 0 := by
  ext j
  have := h (Pi.single j 1)
  rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm, single_dotProduct] at this
  simpa using this

theorem hasSig_complement : ∀ (n₁ : ℕ) (M : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) ℂ) (X Y : Fin (n₁ + 2) → ℂ)
    (ι : Matrix (Fin (n₁ + 2)) (Fin n₁) ℂ) (r s : ℕ), HasSig M r s → 1 ≤ r → 1 ≤ s →
    X ⬝ᵥ M *ᵥ star X = 0 → Y ⬝ᵥ M *ᵥ star Y = 0 → X ⬝ᵥ M *ᵥ star Y ≠ 0 →
    (∀ u, (ι *ᵥ u) ⬝ᵥ M *ᵥ star X = 0 ∧ (ι *ᵥ u) ⬝ᵥ M *ᵥ star Y = 0) → Function.Injective ι.mulVec →
    HasSig (ιᵀ * M * ι.map star) (r - 1) (s - 1) := by
  intro n₁ M X Y ι r s hs _ _ hXX hYY hXY horth hinj
  set c := X ⬝ᵥ M *ᵥ star Y with hc
  set Y' : Fin (n₁ + 2) → ℂ := (star c)⁻¹ • Y with hY'
  have hsY : star Y' = c⁻¹ • star Y := by
    rw [hY', star_smul, star_inv₀, star_star]
  have hXY' : X ⬝ᵥ M *ᵥ star Y' = 1 := by
    rw [hsY, mulVec_smul, dotProduct_smul, smul_eq_mul, ← hc, inv_mul_cancel₀ hXY]
  have hYY' : Y' ⬝ᵥ M *ᵥ star Y' = 0 := by
    rw [hsY, mulVec_smul, dotProduct_smul, hY', smul_dotProduct, hYY]; simp
  have hιX : ιᵀ *ᵥ (M *ᵥ star X) = 0 := transpose_mulVec_eq_zero ι _ fun u => (horth u).1
  have hιY : ιᵀ *ᵥ (M *ᵥ star Y') = 0 := by
    rw [hsY, mulVec_smul, mulVec_smul, transpose_mulVec_eq_zero ι _ fun u => (horth u).2, smul_zero]
  obtain ⟨P, hP⟩ := exists_left_inverse ι hinj
  exact GlobalTheory.PlaneSig.hasSig_complement_plane (n₁ + 2) n₁ M X Y' ι P r s rfl (conjTranspose_eq_of_hasSig hs)
    hXX hYY' hXY' hιX hιY hP hs

end GlobalTheory.PlaneSkewSig
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightFunctionScalingParabolic
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.StdPar GlobalTheory.ResLine
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ResLine

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem Scales.mul_scales {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {x : Matrix (Fin n) (Fin 1) E}
    {a b : GAd σ J} {l l' : (AF F ⊗[F] E)ˣ} (e : Scales σ J x a l) (e' : Scales σ J x b l') :
    Scales σ J x (a * b) (l * l') := by
  unfold Scales at *
  rw [map_mul, Units.val_mul, Matrix.mul_assoc, e', Matrix.mul_smul, e, smul_smul, Units.val_mul, mul_comm]

theorem iwasawaHeight_isHt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), Data σ J X Y L a h → IsHt (levelAll σ J L a) h ∧ ∀ p l, Scales σ J (col X) p l → ∀ g, h (p * g) = absE F E l * h g := by
  intro F E _ _ _ _ _ σ n J r X Y L a h D
  have law : ∀ p l, Scales σ J (col X) p l → ∀ g, h (p * g) = absE F E l * h g := by
    intro p l e g
    obtain ⟨p', l', e', k, hk, rfl⟩ := D.iwa g
    rw [← mul_assoc, D.ht _ _ (e.mul_scales e') k hk, D.ht _ _ e' k hk, map_mul, NNReal.coe_mul]
  refine ⟨⟨fun g => ?_, (GlobalTheory.T.height_function_compact_level_continuous F E σ n J r X Y L a h D).2, fun k hk => ?_, fun g => ?_⟩, law⟩
  · obtain ⟨p, l, e, k, hk, rfl⟩ := D.iwa g
    rw [D.ht _ _ e k hk]
    have h1 : absE F E l * absE F E l⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    exact NNReal.coe_pos.2 (pos_iff_ne_zero.2 (left_ne_zero_of_mul_eq_one h1))
  · have := D.ht 1 1 (by simp [Scales]) k hk
    simpa using this
  · obtain ⟨p, l, e, k, hk, rfl⟩ := D.iwa g
    refine ⟨k, hk, fun x => ?_⟩
    rw [mul_assoc, law p l e, D.ht _ _ e k hk]

end GlobalTheory.ResLine
end

