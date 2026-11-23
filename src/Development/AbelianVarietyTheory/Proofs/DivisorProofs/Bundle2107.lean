module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1998
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalRingDualNumber
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2017
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CotangentBidualToTangentFunctionInjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1994
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2029
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormSkewHermitianBasisVectorEqSqrtTwo
section
open NumberField MeasureTheory Matrix GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CovTop.VolUp GlobalTheory.CovTop.VolUp.FrameBox

namespace GlobalTheory.CovTop.VolUp.FrameBox

theorem boxEnt_norm_sq_eq {r : ℕ} (d : Fin r → ℝ) (hd : ∀ a, d a = 1 ∨ d a = -1) (z a b : Fin r)
    (hab : (a, b) ≠ (z, z)) :
    ∃ P Q : Fin r × Fin r, P ≠ Q ∧ ∀ p : Fin r × Fin r,
      ‖boxEnt d z a b p.1 p.2‖ ^ 2 = (if p = P then 1 else 0) + (if p = Q then 1 else 0) := by
  have hdd : ‖((d a * d b : ℝ) : ℂ)‖ = 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
    rcases hd a with h | h <;> rcases hd b with h' | h' <;> simp [h, h']
  rcases lt_trichotomy a b with h | h | h
  · refine ⟨(a, b), (b, a), ?_, ?_⟩
    · intro e; simp only [Prod.mk.injEq] at e; exact h.ne e.1
    · rintro ⟨a', b'⟩
      simp only [boxEnt, if_pos h, Prod.mk.injEq]
      split_ifs <;> (try simp only [norm_neg, norm_mul, hdd, Complex.norm_I, norm_one, norm_zero]) <;> first | (norm_num; done) | (rename_i h1 h2; exact absurd (h1.1.symm.trans h2.1) h.ne)
  · subst h
    have haz : a ≠ z := fun e => hab (by rw [e])
    refine ⟨(a, a), (z, z), ?_, ?_⟩
    · intro e; simp only [Prod.mk.injEq] at e; exact haz e.1
    · rintro ⟨a', b'⟩
      simp only [boxEnt, lt_irrefl, if_false, Prod.mk.injEq]
      split_ifs <;> simp_all
  · refine ⟨(b, a), (a, b), ?_, ?_⟩
    · intro e; simp only [Prod.mk.injEq] at e; exact h.ne e.1
    · rintro ⟨a', b'⟩
      simp only [boxEnt, if_neg (not_lt.2 h.le), if_pos h, Prod.mk.injEq]
      split_ifs <;> (try simp only [norm_neg, norm_mul, hdd, Complex.norm_I, norm_one, norm_zero]) <;> first | (norm_num; done) | (rename_i h1 h2; exact absurd (h1.1.symm.trans h2.1) h.ne)

theorem norm_boxVec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (d : Ψ → Fin r → ℝ) (z : Fin r), (∀ τ a, d τ a = 1 ∨ d τ a = -1) → ∀ k, ‖boxVec d z k‖ = √2 := by
  intro E _ _ _ r Ψ d z hd k
  obtain ⟨τ, ⟨⟨a, b⟩, hab⟩⟩ := k
  obtain ⟨P, Q, hPQ, hPn⟩ := boxEnt_norm_sq_eq (d τ) (hd τ) z a b hab
  rw [EuclideanSpace.norm_eq]
  congr 1
  rw [Fintype.sum_prod_type, Finset.sum_eq_single τ]
  · have : ∀ p : Fin r × Fin r, ‖(boxVec d z ⟨τ, ⟨(a, b), hab⟩⟩) (τ, p)‖ ^ 2 =
        (if p = P then 1 else 0) + (if p = Q then 1 else 0) := by
      intro p
      rw [← hPn p]
      simp [boxVec]
    simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    norm_num
  · intro τ' _ hτ'
    apply Finset.sum_eq_zero
    intro p _
    simp [boxVec, hτ']
  · simp

end GlobalTheory.CovTop.VolUp.FrameBox
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginLocalRingNoetherianFreeUnitSectionConormal
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CoordsOrigin

noncomputable section

namespace GlobalTheory.CoordsOrigin
variable {R : Type} [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G]

theorem constO_eq_strMap : constO G = (GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateCharacterSystems.strMap G).hom := by
  ext r
  rw [GlobalTheory.HodgeTateCompare.strMap_eq]
  have h1 : (StructureSheaf.toStalk R (G.hom (origin G))).hom r =
      ((Spec (CommRingCat.of R)).presheaf.germ ⊤ (G.hom (origin G)) trivial).hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) := by
    rw [Scheme.ΓSpecIso_inv]
    rfl
  have h2 := congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))
    (Scheme.Hom.germ_stalkMap G.hom ⊤ (origin G) trivial)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
  change _ = (G.hom.stalkMap (origin G)).hom ((StructureSheaf.toStalk R (G.hom (origin G))).hom r)
  rw [h1, h2]
  simp [constO, Scheme.Hom.appLE]
  first
    | (erw [CommRingCat.comp_apply, TopCat.Presheaf.germ_res_apply]; done)
    | (erw [CommRingCat.comp_apply, TopCat.Presheaf.germ_res_apply]; rfl)
    | (rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Category.assoc, TopCat.Presheaf.germ_res]; rfl)
    | (simp only [← CommRingCat.comp_apply, Category.assoc, TopCat.Presheaf.germ_res]; rfl)

theorem free_finite_cotangent_of_eq [Smooth G.hom] (φ : R →+* G.left.presheaf.stalk (origin G))
    (hφ : φ = (GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateCharacterSystems.strMap G).hom) :
    letI : Algebra R (G.left.presheaf.stalk (origin G)) := φ.toAlgebra
    Module.Free R (RingHom.ker (evO G)).Cotangent ∧ Module.Finite R (RingHom.ker (evO G)).Cotangent := by
  subst hφ
  obtain ⟨h1, h2⟩ := GlobalTheory.HodgeTateCompare.finite_projective_of_smooth (G := G)
  change Module.Free R (GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateCharacterSystems.Cotangent G) ∧ Module.Finite R (GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateCharacterSystems.Cotangent G)
  exact ⟨Module.free_of_flat_of_isLocalRing, h1⟩

end GlobalTheory.CoordsOrigin

theorem GlobalTheory.CoordsOrigin.noetherian_free_cotangent : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (G : Over (Sp R)) [GrpObj G], Smooth G.hom → IsNoetherianRing (G.left.presheaf.stalk (origin G)) ∧
      (letI : Algebra R (G.left.presheaf.stalk (origin G)) := (constO G).toAlgebra;
        Module.Free R (RingHom.ker (evO G)).Cotangent ∧ Module.Finite R (RingHom.ker (evO G)).Cotangent) := by
  intro R _ _ _ G _ hs
  haveI := hs
  haveI : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  exact ⟨inferInstance, GlobalTheory.CoordsOrigin.free_finite_cotangent_of_eq G _ (GlobalTheory.CoordsOrigin.constO_eq_strMap G)⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicardClassEqZeroOfZeroDenseOpenAndSectionOpen
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue

theorem bijective_appLE_ι {Z : Scheme.{0}} (O W : Z.Opens) (hW : W ≤ O) (W' : O.toScheme.Opens)
    (h : W' = O.ι ⁻¹ᵁ W) : Function.Bijective (O.ι.appLE W W' h.le) := by
  subst h
  have : IsIso (O.ι.app W) := Scheme.Hom.isIso_app _ _ (by simpa using hW)
  rw [← Scheme.Hom.app_eq_appLE]
  exact ConcreteCategory.bijective_of_isIso _

theorem eq_zero_of_pull_eq_zero : ∀ (T Z : Scheme.{0}) [IsIntegral T] [IsLocallyNoetherian T], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme T → ∀ (U : T.Opens), (U : Set T).Nonempty → ∀ (p : Z ⟶ T) (O : Z.Opens) (e : T ⟶ O.toScheme), Smooth (O.ι ≫ p) → GeometricallyIntegral (O.ι ≫ p) → e ≫ O.ι ≫ p = 𝟙 _ → O ⊔ p ⁻¹ᵁ U = ⊤ → ∀ c : Pic Z, GlobalTheory.CechPic.pull O.ι c = 0 → GlobalTheory.CechPic.pull (p ⁻¹ᵁ U).ι c = 0 → c = 0 := by
  intro T Z _ _ hT U hU p O e hs hg he hcov
  refine _root_.GlobalTheory.CechPic.eq_zero_of_pull_eq_zero_of_units_split Z O (p ⁻¹ᵁ U) hcov fun F => ?_
  have h1 : (O.ι ≫ p) ⁻¹ᵁ U = O.ι ⁻¹ᵁ (O ⊓ p ⁻¹ᵁ U) := by
    rw [Scheme.Hom.preimage_inf, Scheme.Opens.ι_preimage_self, top_inf_eq, Scheme.Hom.comp_preimage]
  have h2 : (⊤ : O.toScheme.Opens) = O.ι ⁻¹ᵁ O := by simp
  have b1 := bijective_appLE_ι O (O ⊓ p ⁻¹ᵁ U) inf_le_left _ h1
  have b2 := bijective_appLE_ι O O le_rfl _ h2
  obtain ⟨G, w, hGw⟩ := _root_.GlobalTheory.UnitAboveOpen.exists_eq_res_mul_pullU T O hT U hU (O.ι ≫ p) e hs hg he
    (Units.map (O.ι.appLE (O ⊓ p ⁻¹ᵁ U) _ h1.le).hom.toMonoidHom F)
  let ε := RingEquiv.ofBijective (O.ι.appLE O ⊤ h2.le).hom b2
  refine ⟨Units.map ε.symm.toMonoidHom G, pullU p U w, ?_⟩
  apply Units.ext
  apply b1.1
  have hv := congrArg Units.val hGw
  have hG : (O.ι.appLE O ⊤ h2.le).hom (ε.symm G) = G := ε.apply_symm_apply _
  change (O.ι.appLE (O ⊓ p ⁻¹ᵁ U) _ h1.le).hom F =
    O.toScheme.presheaf.map (homOfLE le_top).op (G : Γ(O, ⊤)) * (O.ι ≫ p).app U (w : Γ(T, U)) at hv
  change (O.ι.appLE (O ⊓ p ⁻¹ᵁ U) _ h1.le).hom F = (O.ι.appLE (O ⊓ p ⁻¹ᵁ U) _ h1.le).hom
    (Z.presheaf.map (homOfLE inf_le_left).op (ε.symm G) *
      Z.presheaf.map (homOfLE inf_le_right).op (p.app U (w : Γ(T, U))))
  rw [hv, map_mul, ← hG]
  congr 1
  · rw [hG]
    conv_lhs => rw [← hG]
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  · rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE, Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE,
      Scheme.Hom.appLE_comp_appLE]

end GlobalTheory.PicGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicardClassLocallyTrivialOfTrivialSmoothNormalCo
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LocalTriv

theorem hartogs_chart : ∀ (Y : Scheme.{0}) (V : Y.Opens) (hV : IsAffineOpen V), IsLocallyNoetherian (Sp Γ(Y, V)) → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y → ∀ U : (Sp Γ(Y, V)).Opens, (∀ p : Sp Γ(Y, V), ringKrullDim (Y.presheaf.stalk (hV.fromSpec p)) ≤ 1 → p ∈ U) → Function.Bijective ((Sp Γ(Y, V)).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom := by
  intro Y V hV hLN hY U hU
  have hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp Γ(Y, V)) := fun p => by
    let e := (asIso (hV.fromSpec.stalkMap p)).commRingCatIsoToRingEquiv
    obtain ⟨h1, h2⟩ := hY (hV.fromSpec p)
    haveI := h1
    haveI := h2
    haveI : IsDomain ((Sp Γ(Y, V)).presheaf.stalk p) := MulEquiv.isDomain _ e.symm.toMulEquiv
    exact ⟨inferInstance, IsIntegrallyClosed.of_equiv e⟩
  have hb := ((GlobalTheory.extension_over_codim_two (Sp Γ(Y, V)) hN).1 U fun p hp => hU p (by
    let e := (asIso (hV.fromSpec.stalkMap p)).commRingCatIsoToRingEquiv
    exact (ringKrullDim_eq_of_ringEquiv e).trans_le hp)).1 ⊤
  have key : ∀ (V' : (Sp Γ(Y, V)).Opens) (_ : V' = U) (h' : V' ≤ ⊤),
      Function.Bijective (resG (Sp Γ(Y, V)) h') →
        Function.Bijective ((Sp Γ(Y, V)).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom := by
    rintro _ rfl _ h
    exact h
  exact key _ (top_inf_eq U) _ hb

theorem factor_locus : ∀ (X T : Scheme.{0}) (W : X.Opens) (c : Pic W.toScheme) (j : T ⟶ X) [IsOpenImmersion j] (V : (j ⁻¹ᵁ W).toScheme.Opens), IsLocus (GlobalTheory.CechPic.pull (j ∣_ W) c) V → ∀ N : X.Opens, (∀ w ∈ N ⊓ W, ∃ z ∈ V, j ((j ⁻¹ᵁ W).ι z) = w) → GlobalTheory.CechPic.pull (X.homOfLE (inf_le_right : N ⊓ W ≤ W)) c = 0 := by
  intro X T W c j _ V hV N hN
  have hz : ∀ z : (N ⊓ W).toScheme, ∃ z' ∈ V, (j ∣_ W) z' = X.homOfLE (inf_le_right : N ⊓ W ≤ W) z := by
    intro z
    obtain ⟨z', hz'V, hz'⟩ := hN ((N ⊓ W).ι z) z.2
    refine ⟨z', hz'V, W.ι.isOpenEmbedding.injective ?_⟩
    have e1 : W.ι ((j ∣_ W) z') = j ((j ⁻¹ᵁ W).ι z') :=
      congrArg (fun f => f.base z') (morphismRestrict_ι j W)
    have e2 : W.ι (X.homOfLE (inf_le_right : N ⊓ W ≤ W) z) = (N ⊓ W).ι z :=
      congrArg (fun f => f.base z) (X.homOfLE_ι (inf_le_right : N ⊓ W ≤ W))
    exact e1.trans (hz'.trans e2.symm)
  let k := IsOpenImmersion.lift (j ∣_ W) (X.homOfLE (inf_le_right : N ⊓ W ≤ W)) (by
    rintro _ ⟨z, rfl⟩
    obtain ⟨z', -, h⟩ := hz z
    exact ⟨z', h⟩)
  have hk : k ≫ (j ∣_ W) = X.homOfLE (inf_le_right : N ⊓ W ≤ W) := IsOpenImmersion.lift_fac _ _ _
  rw [← hk, pull_comp]
  refine _root_.GlobalTheory.LocusPull.locus_pull.2 _ _ k _ V hV fun z => ?_
  obtain ⟨z', hz'V, h⟩ := hz z
  have hkz : k z = z' := (j ∣_ W).isOpenEmbedding.injective (by
    have e : (j ∣_ W) (k z) = X.homOfLE (inf_le_right : N ⊓ W ≤ W) z := congrArg (fun f => f.base z) hk
    exact e.trans h.symm)
  rw [hkz]
  exact hz'V

theorem locally_trivial : ∀ (X Y : Scheme.{0}) [IsLocallyNoetherian X] (q : Y ⟶ X) [Smooth q] [Surjective q], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y → ∀ W : X.Opens, (∀ z : Y, ringKrullDim ((Y).presheaf.stalk z) ≤ 1 → z ∈ q ⁻¹ᵁ W) → ∀ c : Pic W.toScheme, GlobalTheory.CechPic.pull (q ∣_ W) c = 0 → ∀ x : X, ∃ N : X.Opens, x ∈ N ∧ GlobalTheory.CechPic.pull (X.homOfLE (inf_le_right : N ⊓ W ≤ W)) c = 0 := by
  intro X Y _ q _ _ hY W hW c hc x
  obtain ⟨y, rfl⟩ := q.surjective x
  obtain ⟨N0, hN0, hx0, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (show q y ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨N1, hN1, hy1, hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
    (show y ∈ q ⁻¹ᵁ N0 from hx0)
  have hA0 : IsAffineOpen N0 := hN0
  have hA1 : IsAffineOpen N1 := hN1
  have hB : IsNoetherianRing Γ(X, N0) := IsLocallyNoetherian.component_noetherian ⟨N0, hN0⟩
  let g : Γ(X, N0) →+* Γ(Y, N1) := (q.appLE N0 N1 hle).hom
  have hg : g.Flat := HasRingHomProperty.appLE @Flat q inferInstance ⟨N0, hN0⟩ ⟨N1, hN1⟩ hle
  have hsq : spMap g ≫ hA0.fromSpec = hA1.fromSpec ≫ q := IsAffineOpen.SpecMap_appLE_fromSpec q hA0 hA1 hle
  have hpt : ∀ p, hA0.fromSpec (spMap g p) = q (hA1.fromSpec p) := fun p => by
    have := congrArg (fun f => f.base p) hsq
    simpa using this
  have hLN : IsLocallyNoetherian (Sp Γ(Y, N1)) := LocallyOfFiniteType.isLocallyNoetherian (hA1.fromSpec ≫ q)
  let W0 : (Sp Γ(X, N0)).Opens := hA0.fromSpec ⁻¹ᵁ W
  have hbij := hartogs_chart Y N1 hA1 hLN hY (spMap g ⁻¹ᵁ W0) fun p hp => by
    show hA0.fromSpec (spMap g p) ∈ W
    rw [hpt]
    exact hW _ hp
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  let M := L.pull (hA0.fromSpec ∣_ W)
  have hM : M.IsLB := pull_isLB hL _
  have hk : spMap g ⁻¹ᵁ W0 ≤ hA1.fromSpec ⁻¹ᵁ (q ⁻¹ᵁ W) := fun p hp => by
    show q (hA1.fromSpec p) ∈ W
    rw [← hpt]
    exact hp
  have hcomp : (spMap g ∣_ W0) ≫ (hA0.fromSpec ∣_ W) = hA1.fromSpec.resLE (q ⁻¹ᵁ W) _ hk ≫ (q ∣_ W) := by
    rw [← cancel_mono W.ι]
    simp only [Category.assoc, morphismRestrict_ι, Scheme.Hom.resLE_comp_ι_assoc]
    exact (morphismRestrict_ι_assoc (spMap g) W0 hA0.fromSpec).trans (congrArg _ hsq)
  have htriv : Triv (M.pull (spMap g ∣_ W0)) := by
    have h0 : cls _ (pull_isLB hM (spMap g ∣_ W0)) = 0 := by
      rw [cls_pull hM, cls_pull hL, ← pull_comp, hcomp, pull_comp, hc, map_zero]
    exact (cls_eq_zero_iff _).1 h0
  obtain ⟨y1, rfl⟩ : y ∈ Set.range hA1.fromSpec := hA1.range_fromSpec ▸ hy1
  obtain ⟨s, D, hyD, hD⟩ := _root_.GlobalTheory.FlatTrivSec.exists_sec_near Γ(X, N0) Γ(Y, N1) g hg W0 hbij M hM htriv y1
  let N : X.Opens := ⟨q '' (hA1.fromSpec '' D), q.isOpenMap _ (hA1.fromSpec.isOpenEmbedding.isOpenMap _ D.isOpen)⟩
  refine ⟨N, ⟨_, ⟨y1, hyD, rfl⟩, rfl⟩, ?_⟩
  refine factor_locus X _ W _ hA0.fromSpec (ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s) ⟨M, hM, s, cls_pull hL _ hM, rfl⟩ N ?_
  rintro w ⟨⟨_, ⟨d, hd, rfl⟩, rfl⟩, hwW⟩
  have hdW : d ∈ spMap g ⁻¹ᵁ W0 := by
    show hA0.fromSpec (spMap g d) ∈ W
    rw [hpt]
    exact hwW
  refine ⟨(spMap g ∣_ W0) ⟨d, hdW⟩, hD ⟨d, hdW⟩ hd, ?_⟩
  have e : W0.ι ((spMap g ∣_ W0) ⟨d, hdW⟩) = spMap g d :=
    congrArg (fun f => f.base ⟨d, hdW⟩) (morphismRestrict_ι (spMap g) W0)
  exact (congrArg hA0.fromSpec.base e).trans (hpt d)

end GlobalTheory.LocalTriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PinchedChartOffClosedPartFromBase
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Pinch

theorem isLocalization_away_of_absorb {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
    (hinj : Function.Injective (algebraMap R R')) (c : Ideal R)
    (hc : ∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) {f : R} (hf : f ∈ c) :
    IsLocalization.Away f (Localization.Away (algebraMap R R' f)) := by
  have hmap : ∀ a : R, algebraMap R (Localization.Away (algebraMap R R' f)) a =
      algebraMap R' (Localization.Away (algebraMap R R' f)) (algebraMap R R' a) := fun a =>
    IsScalarTower.algebraMap_apply R R' _ a
  refine (isLocalization_iff _ _).2 ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    rw [hmap, map_pow, map_pow]
    exact IsUnit.pow n (IsLocalization.Away.algebraMap_isUnit (algebraMap R R' f))
  · intro z
    obtain ⟨⟨r', ⟨_, n, rfl⟩⟩, hz⟩ := IsLocalization.surj (Submonoid.powers (algebraMap R R' f)) z
    obtain ⟨y, -, hy⟩ := hc f hf r'
    refine ⟨⟨y, ⟨f ^ (n + 1), n + 1, rfl⟩⟩, ?_⟩
    simp only at hz ⊢
    rw [hmap, hmap, hy, map_pow, map_pow, pow_succ, map_mul, ← hz, map_pow]
    ring
  · intro a b h
    rw [hmap, hmap] at h
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers (algebraMap R R' f)) h
    refine ⟨⟨f ^ k, k, rfl⟩, hinj ?_⟩
    simp only [map_mul, map_pow] at hk ⊢
    exact hk

theorem pinched_off : ∀ (R : Type) [CommRing R] (R' : Type) [CommRing R'] [Algebra R R'], Function.Injective (algebraMap R R') → ∀ c : Ideal R, (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → ∀ (g : ℕ) (B' C Y : Scheme.{0}) (b' : B' ⟶ Sp R') (e : C ⟶ Sp (R ⧸ c)) (i : Y ⟶ B') (q : Y ⟶ C), SmoothOfRelativeDimension g b' → ∀ x : B', (b' ≫ spMap (algebraMap R R')) x ∉ Set.range (spMap (Ideal.Quotient.mk c)) → GlobalTheory.Pinch.Pinched g (spMap (algebraMap R R')) (spMap (Ideal.Quotient.mk c)) b' e i q x := by
  intro R _ R' _ _ hinj c hc g B' C Y b' e i q hsm x hx
  obtain ⟨f, hfc, hfx⟩ : ∃ f ∈ c, f ∉ ((b' ≫ spMap (algebraMap R R')) x).asIdeal := by
    by_contra hno
    push_neg at hno
    apply hx
    have hr : Set.range (spMap (Ideal.Quotient.mk c)) =
        PrimeSpectrum.zeroLocus (RingHom.ker (Ideal.Quotient.mk c)) :=
      range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective
    rw [hr, Ideal.mk_ker]
    exact hno
  haveI : IsLocalization.Away f (Localization.Away (algebraMap R R' f)) :=
    isLocalization_away_of_absorb hinj c hc hfc
  let l' : Sp (Localization.Away (algebraMap R R' f)) ⟶ Sp R' := spMap (algebraMap R' _)
  let h : Sp (Localization.Away (algebraMap R R' f)) ⟶ Sp R := spMap (algebraMap R _)
  haveI : IsOpenImmersion l' := IsOpenImmersion.of_isLocalization (algebraMap R R' f)
  haveI : IsOpenImmersion h := IsOpenImmersion.of_isLocalization f
  have hcomp : l' ≫ spMap (algebraMap R R') = h := by
    simp only [l', h, spMap, ← Spec.map_comp]
    congr 1
  have hrange : Set.range h = (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) :=
    PrimeSpectrum.localization_away_comap_range _ f
  have hrange' : Set.range l' =
      (PrimeSpectrum.basicOpen (algebraMap R R' f) : Set (PrimeSpectrum R')) :=
    PrimeSpectrum.localization_away_comap_range _ _
  let j : pullback b' l' ⟶ B' := pullback.fst b' l'
  let u : pullback b' l' ⟶ Sp R := pullback.snd b' l' ≫ h
  have hju : j ≫ b' ≫ spMap (algebraMap R R') = u := by
    simp only [j, u, ← hcomp]
    rw [← Category.assoc, pullback.condition, Category.assoc]
  have hsmu : SmoothOfRelativeDimension g u := by
    haveI : SmoothOfRelativeDimension g (pullback.snd b' l') :=
      (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback
        (IsPullback.of_hasPullback b' l') hsm
    haveI : SmoothOfRelativeDimension 0 h := inferInstance
    have := smoothOfRelativeDimension_comp g 0 (pullback.snd b' l') h
    simpa using this
  have hD : ∀ t : ↥(pullback b' l'), f ∉ (u t).asIdeal := fun t => by
    have : u t ∈ Set.range h := ⟨pullback.snd b' l' t, rfl⟩
    rw [hrange] at this
    exact this
  have hEmpty : ∀ (T : Scheme.{0}) (a : T ⟶ pullback b' l') (a' : T ⟶ Sp (R ⧸ c)),
      a ≫ u = a' ≫ spMap (Ideal.Quotient.mk c) → IsEmpty T := by
    intro T a a' w
    refine ⟨fun t => hD (a t) ?_⟩
    have e1 : u (a t) = spMap (Ideal.Quotient.mk c) (a' t) := by
      rw [← Scheme.Hom.comp_apply, w, Scheme.Hom.comp_apply]
    rw [e1]
    show Ideal.Quotient.mk c f ∈ (a' t).asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hfc]
    exact Ideal.zero_mem _
  have w1 : 𝟙 (pullback b' l') ≫ u = (j ≫ b') ≫ spMap (algebraMap R R') := by
    rw [Category.id_comp, Category.assoc, hju]
  have w2 : Scheme.emptyTo (pullback b' l') ≫ u = (Scheme.emptyTo C ≫ e) ≫ spMap (Ideal.Quotient.mk c) :=
    Scheme.empty_ext _ _
  refine ⟨pullback b' l', pullback b' l', ∅, u, 𝟙 _, j, Scheme.emptyTo _, Scheme.emptyTo C, hsmu,
    ⟨⟨w1⟩, ⟨PullbackCone.IsLimit.mk w1 (fun s => s.fst) (fun s => Category.comp_id _) (fun s => ?_)
      (fun s m h1 _ => by simpa using h1)⟩⟩, inferInstance, ?_,
    ⟨⟨w2⟩, ⟨PullbackCone.IsLimit.mk w2
      (fun s => haveI := hEmpty _ _ _ s.condition; isInitialOfIsEmpty.to _)
      (fun s => by haveI := hEmpty _ _ _ s.condition; exact isInitialOfIsEmpty.hom_ext _ _)
      (fun s => by haveI := hEmpty _ _ _ s.condition; exact isInitialOfIsEmpty.hom_ext _ _)
      (fun s m _ _ => by haveI := hEmpty _ _ _ s.condition; exact isInitialOfIsEmpty.hom_ext _ _)⟩⟩, ?_⟩
  · have hr : Set.range s.snd ⊆ Set.range l' := by
      rintro _ ⟨t, rfl⟩
      rw [hrange']
      have e1 : spMap (algebraMap R R') (s.snd t) = u (s.fst t) := by
        rw [← Scheme.Hom.comp_apply, ← s.condition, Scheme.Hom.comp_apply]
      have := hD (s.fst t)
      rw [← e1] at this
      exact this
    have hl : IsOpenImmersion.lift l' s.snd hr ≫ l' = s.snd := IsOpenImmersion.lift_fac l' s.snd hr
    have hl2 : IsOpenImmersion.lift l' s.snd hr = s.fst ≫ pullback.snd b' l' := by
      rw [← cancel_mono h, ← hcomp, ← Category.assoc, hl, ← s.condition]
      show s.fst ≫ (pullback.snd b' l' ≫ h) = _
      rw [← hcomp]
      simp only [Category.assoc]
    show s.fst ≫ j ≫ b' = s.snd
    rw [← hl, hl2]
    exact congrArg (s.fst ≫ ·) pullback.condition
  · rw [IsOpenImmersion.range_pullbackFst l' b']
    show b' x ∈ Set.range l'
    rw [hrange']
    exact hfx
  · intro T a a' _
    haveI : IsEmpty T := ⟨fun t => isEmptyElim (a' t)⟩
    exact ⟨isInitialOfIsEmpty.to Y, isInitialOfIsEmpty.hom_ext _ _, isInitialOfIsEmpty.hom_ext _ _⟩

end GlobalTheory.Pinch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PinchedChartsRestrictMatchingOpens
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Pinch

theorem restrict_pinched : ∀ (g : ℕ) (S S' Z B' C Y : Scheme.{0}) (s' : S' ⟶ S) (z : Z ⟶ S) (b' : B' ⟶ S') (e : C ⟶ Z) (i : Y ⟶ B') (q : Y ⟶ C), IsPullback i (q ≫ e) (b' ≫ s') z → IsPullback q (i ≫ b') (e ≫ z) s' → ∀ (V' : B'.Opens) (V : C.Opens), i ⁻¹ᵁ V' = q ⁻¹ᵁ V → ∃ (q₀ : (i ⁻¹ᵁ V').toScheme ⟶ V.toScheme), IsPullback (i ∣_ V') (q₀ ≫ V.ι ≫ e) ((V'.ι ≫ b') ≫ s') z ∧ IsPullback q₀ ((i ∣_ V') ≫ V'.ι ≫ b') ((V.ι ≫ e) ≫ z) s' ∧ ∀ x : V'.toScheme, GlobalTheory.Pinch.Pinched g s' z (V'.ι ≫ b') (V.ι ≫ e) (i ∣_ V') q₀ x → GlobalTheory.Pinch.Pinched g s' z b' e i q (V'.ι x) := by
  intro g S S' Z B' C Y s' z b' e i q h₁ h₂ V' V hV
  refine ⟨(Y.isoOfEq hV).hom ≫ (q ∣_ V), ?_, ?_, ?_⟩
  · have hq : ((Y.isoOfEq hV).hom ≫ (q ∣_ V)) ≫ V.ι ≫ e = (i ⁻¹ᵁ V').ι ≫ q ≫ e := by
      simp [morphismRestrict_ι_assoc, Scheme.isoOfEq_hom_ι_assoc]
    rw [hq, Category.assoc]
    exact (isPullback_morphismRestrict i V').paste_vert h₁
  · have P := (isPullback_morphismRestrict q V).paste_vert h₂
    refine IsPullback.of_iso P (Y.isoOfEq hV).symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · simp [morphismRestrict_ι_assoc, Scheme.isoOfEq_inv_ι_assoc]
    · simp
    · simp
  · intro x hx
    obtain ⟨U, U', W₀, u, p, j, n, k, hu, hp, hj, hx, hn, hl⟩ := hx
    refine ⟨U, U', W₀, u, p, j ≫ V'.ι, n, k ≫ V.ι, hu, by simpa using hp, inferInstance, ?_, by simpa using hn, ?_⟩
    · obtain ⟨w, rfl⟩ := hx
      exact ⟨w, rfl⟩
    · intro T a a' haa
      obtain ⟨y, hy₁, hy₂⟩ := hl T a a' haa
      refine ⟨y ≫ (i ⁻¹ᵁ V').ι, ?_, ?_⟩
      · rw [Category.assoc, ← morphismRestrict_ι, ← Category.assoc, hy₁, Category.assoc]
      · have hq : (Y.isoOfEq hV).hom ≫ (q ∣_ V) ≫ V.ι = (i ⁻¹ᵁ V').ι ≫ q := by
          simp [morphismRestrict_ι, Scheme.isoOfEq_hom_ι_assoc]
        rw [Category.assoc, ← hq, reassoc_of% hy₂]

end GlobalTheory.Pinch
end
end

