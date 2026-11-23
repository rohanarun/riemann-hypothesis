module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1997
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1971
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitMkOfFormallyUnramified
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2021
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0536
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2025
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsReducedNormalModelGenericCorrespondence
section
noncomputable section

namespace GlobalTheory.UPel.HT.ES

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

theorem isReduced_of_pReg_of_factor (p : ℕ) {Y₀ Y : Scheme.{0}} [IsReduced Y₀] (i : Y₀ ⟶ Y) [IsOpenImmersion i]
    (hp : ∀ (U : Y.Opens) (f : Γ(Y, U)), (p : Γ(Y, U)) * f = 0 → f = 0)
    (hfac : ∀ (S : Scheme.{0}) (f : S ⟶ Y), IsUnit ((p : ℕ) : Γ(S, ⊤)) → ∃ f₀ : S ⟶ Y₀, f₀ ≫ i = f) :
    IsReduced Y := by

  have haff : ∀ (V : Y.Opens), IsAffineOpen V → ∀ g : Γ(Y, V), IsNilpotent g → g = 0 := by
    intro V hV g hg
    let q : Γ(Y, V) := (p : Γ(Y, V))
    let O := Y.basicOpen q
    let ρ : Γ(Y, V) →+* Γ(Y, O) := (Y.presheaf.map (homOfLE (Y.basicOpen_le q)).op).hom
    letI : Algebra Γ(Y, V) Γ(Y, O) := ρ.toAlgebra
    haveI : IsLocalization.Away q Γ(Y, O) := hV.isLocalization_basicOpen q
    have hu : IsUnit ((p : ℕ) : Γ(O.toScheme, ⊤)) := by
      have h1 : IsUnit (algebraMap Γ(Y, V) Γ(Y, O) q) := IsLocalization.Away.algebraMap_isUnit q
      rw [map_natCast] at h1
      have := h1.map (O.topIso.inv.hom)
      rwa [map_natCast] at this
    obtain ⟨f₀, hf₀⟩ := hfac O.toScheme O.ι hu
    haveI : IsOpenImmersion (f₀ ≫ i) := hf₀ ▸ inferInstance
    haveI : IsOpenImmersion f₀ := IsOpenImmersion.of_comp f₀ i
    haveI : IsReduced O.toScheme := isReduced_of_isOpenImmersion f₀
    haveI : _root_.IsReduced Γ(Y, O) :=
      isReduced_of_injective (O.topIso.inv.hom) (O.topIso.commRingCatIsoToRingEquiv.symm.injective)
    have h0 : algebraMap Γ(Y, V) Γ(Y, O) g = 0 := (hg.map (algebraMap Γ(Y, V) Γ(Y, O))).eq_zero
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers q) _ g).1 h0
    have hk' : q ^ k * g = 0 := hk
    clear hk h0
    induction k with
    | zero => simpa using hk'
    | succ k ih => exact ih (hp V _ (by rw [pow_succ', _root_.mul_assoc] at hk'; exact hk'))
  refine ⟨fun U => ⟨fun f hf => ?_⟩⟩
  refine Y.sheaf.eq_of_locally_eq' (fun V : {V : Y.affineOpens // V.1 ≤ U} => V.1.1) U
    (fun V => homOfLE V.2) ?_ f 0 fun V => ?_
  · intro y hy
    obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVU⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hy U.isOpen
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨V, hV⟩, hVU⟩, hyV⟩
  · rw [map_zero]
    exact haff V.1.1 V.1.2 _ (hf.map _)

theorem isReduced_normalModel_of_generic : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (M : Model b N) (Y₀ : Scheme.{0}) (s₀ : Y₀ ⟶ M.X) (gs : Y₀ ⟶ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme), gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = s₀ → Etale gs → ∀ (Y : Scheme.{0}) (s : Y ⟶ M.X) (i : Y₀ ⟶ Y), IsOpenImmersion i → i ≫ s = s₀ → Flat (s ≫ M.s) → (∀ (S : Scheme.{0}) (f : S ⟶ Y), IsUnit ((p : ℕ) : Γ(S, ⊤)) → ∃ f₀ : S ⟶ Y₀, f₀ ≫ i = f) → IsReduced Y := by
  intro p _ D R _ _ _ _ b N _ M Y₀ s₀ gs hgs _ Y s i _ _ hfl hfac
  haveI := M.smooth
  haveI : Smooth M.s := SmoothOfRelativeDimension.smooth (D.a * (D.n - 1)) M.s
  haveI : IsReduced Y₀ := GlobalTheory.isReduced_of_smooth_of_isReduced (gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι ≫ M.s)
  have hR : ∀ a : R, (p : R) * a = 0 → a = 0 := fun a ha =>
    (mul_eq_zero.1 ha).resolve_left (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  haveI := hfl
  exact isReduced_of_pReg_of_factor p i (fun U f hf => pReg_of_flat (p := p) (s ≫ M.s) hR U f hf) hfac

end GlobalTheory.UPel.HT.ES
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularLocalRingQuotientOfDetDerivationUnit
section
open IsLocalRing TensorProduct

namespace GlobalTheory.JacobianDerivation

theorem isRegularLocalRing_quotient : ∀ (T : Type) [CommRing T] [IsRegularRing T] (h : ℕ) (f : Fin h → T)
    (D : Fin h → Derivation ℤ T T) (n : Ideal T) [n.IsPrime], (∀ j, f j ∈ n) →
    (Matrix.of fun i j => D i (f j)).det ∉ n →
    IsRegularLocalRing (Localization.AtPrime n ⧸
      (Ideal.span (Set.range f)).map (algebraMap T (Localization.AtPrime n))) := by
  intro T _ _ h f D n _ hf hdet
  classical
  let A := Localization.AtPrime n
  haveI : IsRegularLocalRing A := IsRegularRing.isRegularLocalRing_localization n
  let x : Fin h → A := fun j => algebraMap T A (f j)
  have hx : ∀ j, x j ∈ maximalIdeal A := fun j =>
    (IsLocalization.AtPrime.to_map_mem_maximal_iff A n (f j)).mpr (hf j)

  have hrow0 : ∀ a : Fin h → A, ∑ j, a j * x j ∈ maximalIdeal A ^ 2 →
      ∀ i, ∑ j, a j * algebraMap T A (D i (f j)) ∈ maximalIdeal A := by
    intro a ha i
    obtain ⟨D', hD'⟩ := @GlobalTheory.derivation_extend_localization_atPrime ℤ T A _ _ _ (Ring.toIntAlgebra T) _ (Ring.toIntAlgebra A)
      (@IsScalarTower.of_algebraMap_eq' ℤ T A _ _ _ (Ring.toIntAlgebra T) _ (Ring.toIntAlgebra A)
        (Subsingleton.elim _ _)) n _ _
      { toFun := fun t => algebraMap T A (D i t)
        map_add' := fun s t => by simp
        map_smul' := fun m t => by simp [Algebra.smul_def]
        map_one_eq_zero' := by simp
        leibniz' := fun s t => by simp [Algebra.smul_def] }
    letI : Algebra ℤ A := Ring.toIntAlgebra A
    have hsq : ∀ y ∈ maximalIdeal A ^ 2, D' y ∈ maximalIdeal A := by
      intro y hy
      rw [pow_two] at hy
      refine Submodule.mul_induction_on hy (fun a ha b hb => ?_) (fun y z hy hz => ?_)
      · rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
        exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ ha) (Ideal.mul_mem_right _ _ hb)
      · rw [map_add (f := _)]; exact Ideal.add_mem _ hy hz
    have h1 := hsq _ ha
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at h1
    have h2 : ∀ j, D' (a j * x j) = a j * algebraMap T A (D i (f j)) + x j * D' (a j) := by
      intro j
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, hD']
      rfl
    simp_rw [h2, Finset.sum_add_distrib] at h1
    have h3 : ∑ j, x j * D' (a j) ∈ maximalIdeal A :=
      Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (hx j)
    simpa using Ideal.sub_mem _ h1 h3
  have hind : ∀ a : Fin h → A, ∑ j, a j * x j ∈ maximalIdeal A ^ 2 → ∀ j, a j ∈ maximalIdeal A := by
    intro a ha
    have hrow := hrow0 a ha
    let φ : T →+* ResidueField A := (residue A).comp (algebraMap T A)
    let M : Matrix (Fin h) (Fin h) (ResidueField A) := φ.mapMatrix (Matrix.of fun i j => D i (f j))
    have hM : M.det ≠ 0 := by
      rw [← RingHom.map_det]
      intro h0
      have hu : IsUnit (algebraMap T A (Matrix.of fun i j => D i (f j)).det) :=
        (IsLocalization.AtPrime.isUnit_to_map_iff A n _).mpr hdet
      exact (residue_ne_zero_iff_isUnit _).mpr hu h0
    have hv : M.mulVec (fun j => residue A (a j)) = 0 := by
      funext i
      have := (residue_eq_zero_iff _).mpr (hrow i)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum] at this
      simp only [Matrix.mulVec, dotProduct, M, RingHom.mapMatrix_apply, Matrix.map_apply,
        Matrix.of_apply, Pi.zero_apply, φ, RingHom.comp_apply]
      rw [← this]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, mul_comm]
    intro j
    have := congrFun (Matrix.eq_zero_of_mulVec_eq_zero hM hv) j
    exact (residue_eq_zero_iff _).mp this

  let τ : Fin h → maximalIdeal A := fun i => ⟨x i, hx i⟩
  have hτ : LinearIndependent (ResidueField A) (fun i => (maximalIdeal A).toCotangent (τ i)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    choose a ha using fun j => residue_surjective (g j)
    have h1 : (maximalIdeal A).toCotangent (∑ j, a j • τ j) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, ← hg]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, ← ha j]
      rfl
    rw [Ideal.toCotangent_eq_zero] at h1
    have h2 : ∑ j, a j * x j ∈ maximalIdeal A ^ 2 := by
      simpa [τ] using h1
    rw [← ha i]
    exact (residue_eq_zero_iff _).mpr (hind a h2 i)
  obtain ⟨J, _, t, hs, hd⟩ := GlobalTheory.RegularQuotient.exists_extend A τ hτ
  have hrange : (Set.range fun i => ((τ i : maximalIdeal A) : A)) = Set.range x := rfl
  rw [hrange] at hs
  obtain ⟨hreg, -⟩ := GlobalTheory.RegularQuotient.quot_regular A t x hs hd
  have hmap : (Ideal.span (Set.range f)).map (algebraMap T A) = Ideal.span (Set.range x) := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  show IsRegularLocalRing (A ⧸ (Ideal.span (Set.range f)).map (algebraMap T A))
  rw [hmap]
  exact hreg

end GlobalTheory.JacobianDerivation
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStandardSmoothLocalizationAwayJacobianDvd
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Pinch

theorem isStandardSmoothOfRelativeDimension_localizationAway_of_det_dvd
    (R ν σ : Type) [CommRing R] [Finite ν] [Fintype σ] [DecidableEq σ] (m : σ → ν)
    (hm : Function.Injective m) (F : σ → MvPolynomial ν R) (h : MvPolynomial ν R)
    (hdvd : (Matrix.of fun s t : σ ↦ MvPolynomial.pderiv (m s) (F t)).det ∣ h) :
    Algebra.IsStandardSmoothOfRelativeDimension (Nat.card ν - Nat.card σ) R
      (Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range F)) h)) := by
  classical
  set A := MvPolynomial ν R ⧸ Ideal.span (Set.range F)
  set T := Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range F)) h)
  let P := Algebra.PreSubmersivePresentation.naive (v := F) m hm
  let Q := Algebra.SubmersivePresentation.localizationAway T
    (Ideal.Quotient.mk (Ideal.span (Set.range F)) h)
  have hPjac : P.jacobian = Ideal.Quotient.mk (Ideal.span (Set.range F))
      (Matrix.of fun s t : σ ↦ MvPolynomial.pderiv (m s) (F t)).det := by
    rw [P.jacobian_eq_jacobiMatrix_det, Algebra.Generators.algebraMap_apply]
    have hM : P.jacobiMatrix = Matrix.of fun s t : σ ↦ MvPolynomial.pderiv (m s) (F t) := by
      ext i j
      simp [P]
    rw [hM]
    have : MvPolynomial.aeval P.val = Ideal.Quotient.mkₐ R (Ideal.span (Set.range F)) :=
      MvPolynomial.algHom_ext fun v => by simp [P]
    rw [this]
    rfl
  let P' : Algebra.SubmersivePresentation R T (Unit ⊕ ν) (Unit ⊕ σ) :=
    { __ := Q.toPreSubmersivePresentation.comp P
      jacobian_isUnit := by
        rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
          Algebra.smul_def]
        refine IsUnit.mul ?_ Q.jacobian_isUnit
        rw [hPjac]
        exact isUnit_of_dvd_unit (map_dvd _ (map_dvd _ hdvd))
          (IsLocalization.Away.algebraMap_isUnit _) }
  refine P'.isStandardSmoothOfRelativeDimension ?_
  change (Q.toPreSubmersivePresentation.comp P).dimension = _
  rw [Algebra.PreSubmersivePresentation.dimension_comp_eq_dimension_add_dimension]
  simp [Algebra.Presentation.dimension, P]

end GlobalTheory.Pinch
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaEq
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Obs

theorem isTheta_eq {R R₀ B B₀ B' : Type} [CommRing R] [CommRing R₀] [CommRing B] [Algebra R B] [CommRing B₀]
    [Algebra R₀ B₀] [CommRing B'] [Algebra R B'] {I : Ideal R} {p : B →+* B₀} (hp : Function.Surjective p)
    {α β : B →ₐ[R] B'} {θ₁ θ₂ : Ω[B₀⁄R₀] →+ B'} (h₁ : IsTheta I p α β θ₁) (h₂ : IsTheta I p α β θ₂) :
    θ₁ = θ₂ := by
  ext w
  have hw : w ∈ Submodule.span B₀ (Set.range (D R₀ B₀)) := by
    rw [span_range_derivation]; trivial
  refine Submodule.span_induction (p := fun z _ ↦ θ₁ z = θ₂ z) ?_ ?_ ?_ ?_ hw
  · rintro z ⟨y, rfl⟩
    obtain ⟨b, rfl⟩ := hp y
    rw [h₁.der, h₂.der]
  · rw [map_zero, map_zero]
  · intro y z _ _ hy hz; rw [map_add (f := _), map_add (f := _), hy, hz]
  · intro c z _ hz
    obtain ⟨b, rfl⟩ := hp c
    rw [h₁.smul, h₂.smul, hz]

theorem isSig_eq {R R₀ R₁ : Type} [CommRing R] [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] {I : Ideal R}
    {π : R →+* R₀} (α : Aug I π R₁) {B B₀ : Type} [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀]
    {p : B →+* B₀} (hp : Function.Surjective p) {σ σ' : R₁ ⊗[R₀] B₀ →+ B} (h : α.IsSig p σ) (h' : α.IsSig p σ') :
    σ = σ' := by
  ext x
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul y x =>
    obtain ⟨b, rfl⟩ := hp x
    rw [h, h']
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem isOb2_add : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (w w' : Glob1 F) (c c' : GlobalTheory.CatCoh.H2 (ext R₁ F)), L.IsOb2 α w c → L.IsOb2 α w' c' → L.IsOb2 α (w + w') (c + c') := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α C _ F L w w' c c' h h'
  obtain ⟨θ, σ, z, hθ, hσ, rfl, hz⟩ := h
  obtain ⟨θ', σ', z', hθ', hσ', rfl, hz'⟩ := h'
  refine ⟨θ, σ, z + z', hθ, hσ, (map_add _ _ _).symm, fun T T' T'' a b ↦ ?_⟩
  have eθ : θ T T' T'' a b = θ' T T' T'' a b := isTheta_eq (L.surj T) (hθ T T' T'' a b) (hθ' T T' T'' a b)
  have eσ : σ T'' = σ' T'' := isSig_eq α (L.surj T'') (hσ T'') (hσ' T'')
  obtain ⟨k₁, s₁⟩ := hz T T' T'' a b
  obtain ⟨k₂, s₂⟩ := hz' T T' T'' a b
  have ez : (z + z').1 T T' T'' a b = z.1 T T' T'' a b + z'.1 T T' T'' a b := rfl
  refine ⟨?_, ?_⟩
  · unfold Aug.KerQ at k₁ k₂ ⊢
    rw [ez, map_add (f := _), k₁, k₂, add_zero]
  · rw [ez, map_add (f := _), s₁, eσ, s₂, ← eθ]
    exact (map_add (θ T T' T'' a b) (w.1 T) (w'.1 T)).symm

end GlobalTheory.Obs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopFormFrameBaseCoordinatesAddVariablesEtale
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TopFrameEt

open GlobalTheory.TopForm

theorem appLE_comp_algX' {k : Type} [CommRing k] {X Y : Scheme.{0}} (p : X ⟶ Sp k) (q : Y ⟶ X)
    {U : X.Opens} {W : Y.Opens} (h : W ≤ q ⁻¹ᵁ U) :
    (q.appLE U W h).hom.comp (algX p U) = algX (q ≫ p) W := by
  have e := Scheme.Hom.appLE_comp_appLE q p ⊤ U W le_top h
  exact congrArg (fun f ↦ (CommRingCat.Hom.hom f).comp
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom) e

theorem exists_basis_of_exact {R M₁ M₂ M₃ ι ι' : Type} [CommRing R] [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃]
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) (hf : Function.Injective f) (hex : Function.Exact f g)
    (v : Module.Basis ι R M₁) (w : Module.Basis ι' R M₃) (u : ι' → M₂) (hu : ∀ a, g (u a) = w a) :
    ∃ b : Module.Basis (ι ⊕ ι') R M₂, ∀ j, b j = Sum.elim (fun i ↦ f (v i)) u j := by
  let S : ShortComplex (ModuleCat R) := ShortComplex.mk (ModuleCat.ofHom f) (ModuleCat.ofHom g)
    (by ext x; exact hex.apply_apply_eq_zero x)
  have hS : S.Exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).2 hex
  have hm : Mono S.f := (ModuleCat.mono_iff_injective _).2 hf
  let u' : ι ⊕ ι' → M₂ := Sum.elim (fun i ↦ f (v i)) u
  have hw : (S.g ∘ u' ∘ Sum.inr) = w := funext fun a ↦ hu a
  have hli : LinearIndependent R u' := by
    refine ModuleCat.linearIndependent_leftExact (S := S) (v := v) hS v.linearIndependent ?_ hm ?_
    · rw [hw]; exact w.linearIndependent
    · rfl
  have hsp : ⊤ ≤ Submodule.span R (Set.range u') := by
    refine ModuleCat.span_exact (S := S) (v := v) hS rfl (by rw [v.span_eq]) ?_
    rw [hw, w.span_eq]
  exact ⟨Module.Basis.mk hli hsp, fun j ↦ by simp [u']⟩

theorem isFrame_etale : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ X) (p' : Y ⟶ Sp k), q ≫ p = p' → ∀ (m D : ℕ), SmoothOfRelativeDimension m p → ∀ (ι : Type) (o : Fin D ≃ Fin m ⊕ ι) (U U' : X.Opens) (hU' : U' ≤ U), IsAffineOpen U → ∀ (W W' : Y.Opens) (hW' : W' ≤ W), IsAffineOpen W → IsAffineOpen W' → ∀ (hWU : W ≤ q ⁻¹ᵁ U), W' ≤ q ⁻¹ᵁ U' → ∀ (N : ι → Γ(Y, W)), (MvPolynomial.eval₂Hom (q.appLE U W hWU).hom N).Etale → ∀ (x : Fin m → Γ(X, U)), TopForm.IsFrame (TopForm.dOn p fun i => resG X hU' (x i)) → TopForm.IsFrame (TopForm.dOn p' fun a => resG Y hW' (Sum.elim (fun i => (q.appLE U W hWU).hom (x i)) N (o a))) := by
  intro k _ X Y p q p' hp m D _ ι o U U' hU' hU W W' hW' hW hW'a hWU hW'U' N hN x hx
  subst hp
  have hU'a : IsAffineOpen U' := hx.affine
  have hC := _root_.GlobalTheory.EtaleRestrict.etale_eval₂_res X Y q ι U U' hU' hU hU'a W W' hW' hW hW'a hWU hW'U' N hN
  obtain ⟨bR, hbR⟩ := _root_.GlobalTheory.TopForm.FrameBasis.exists_basis_of_isFrame k X p m ‹_› U' _ hx
  haveI : Finite ι := Finite.of_injective (fun a ↦ o.symm (Sum.inr a))
    (fun a b h ↦ Sum.inr_injective (o.symm.injective h))
  letI : Algebra k Γ(X, U') := (algX p U').toAlgebra
  letI : Algebra k Γ(Y, W') := (algX (q ≫ p) W').toAlgebra
  letI : Algebra Γ(X, U') Γ(Y, W') := (q.appLE U' W' hW'U').hom.toAlgebra
  haveI : IsScalarTower k Γ(X, U') Γ(Y, W') :=
    IsScalarTower.of_algebraMap_eq' (appLE_comp_algX' p q hW'U').symm
  let φ := MvPolynomial.eval₂Hom (q.appLE U' W' hW'U').hom (fun a ↦ resG Y hW' (N a))
  letI : Algebra (MvPolynomial ι Γ(X, U')) Γ(Y, W') := φ.toAlgebra
  haveI : IsScalarTower Γ(X, U') (MvPolynomial ι Γ(X, U')) Γ(Y, W') :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by
      change _ = φ (MvPolynomial.C r)
      simp [φ]; rfl
  haveI : Algebra.Etale (MvPolynomial ι Γ(X, U')) Γ(Y, W') := hC
  obtain ⟨⟨bT, hbT⟩, hsm⟩ := GlobalTheory.EtaleCoordJacobian.exists_basis_of_etale Γ(X, U') Γ(Y, W') ι
  haveI := hsm
  haveI : Subsingleton (Algebra.H1Cotangent Γ(X, U') Γ(Y, W')) :=
    Algebra.FormallySmooth.subsingleton_h1Cotangent
  have hinj : Function.Injective (KaehlerDifferential.mapBaseChange k Γ(X, U') Γ(Y, W')) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨z, rfl⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange k Γ(X, U') Γ(Y, W') y).1 hy
    rw [Subsingleton.elim z 0, map_zero]
  obtain ⟨b, hb⟩ := exists_basis_of_exact
    (KaehlerDifferential.mapBaseChange k Γ(X, U') Γ(Y, W'))
    (KaehlerDifferential.map k Γ(X, U') Γ(Y, W') Γ(Y, W')) hinj
    (KaehlerDifferential.exact_mapBaseChange_map k Γ(X, U') Γ(Y, W'))
    (bR.baseChange Γ(Y, W')) bT (fun a ↦ KaehlerDifferential.D k Γ(Y, W') (resG Y hW' (N a)))
    (fun a ↦ by rw [hbT, KaehlerDifferential.map_D]; simp [φ, RingHom.algebraMap_toAlgebra])
  refine ⟨hW'a, isFreeGen_dForm _ (b.reindex o.symm) fun a ↦ ?_⟩
  rw [Module.Basis.reindex_apply, Equiv.symm_symm, hb]
  rcases o a with i | i
  · simp only [Sum.elim_inl, Module.Basis.baseChange_apply, KaehlerDifferential.mapBaseChange_tmul,
      one_smul, hbR, dFun, KaehlerDifferential.map_D]
    refine congrArg (KaehlerDifferential.D k Γ(Y, W')) ?_
    rw [RingHom.algebraMap_toAlgebra, GlobalTheory.LB.appLE_resG, GlobalTheory.LB.resG_appLE]
  · rfl

end GlobalTheory.TopFrameEt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetFrameEigenbasisBlockAtPoint
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole

namespace GlobalTheory.LogPole

attribute [local instance] Over.cartesianMonoidalCategory Over.braidedCategory


open MonObj in
theorem isUnit_det_of_isCombAtG_vecAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (k : TF.X.F.J) (S : Type) [CommRing S] (z : Sp S ⟶ Y₀ TF.X Z) (hU : ⊤ ≤ (z ≫ toBase TF Z) ⁻¹ᵁ U.1) (hk : ⊤ ≤ (z ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k) (hx : (z ≫ inc₀ TF.X Z) ≫ TF.X.π = z ≫ toBase TF Z) (σ : E →+* ℂ) (C : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S), (∀ i : Fin (Dw.mult σ), IsCombAtG TF.Y.t (z ≫ toBase TF Z) (fun j => spMap (dualMap (ev (z ≫ toBase TF Z) U.1 hU)) ≫ v (e ⟨σ, j⟩)) (C i) (tv (TF.X.F.vecAt k (z ≫ inc₀ TF.X Z) hk hx σ i)).left) → IsUnit C.det := by
  intro E _ _ _ H Dw l Xo c TF Z U n e v hv k S _ z hU hk hx σ C hC
  open scoped CategoryTheory.MonObj in
   set_option synthInstance.maxHeartbeats 1000000 in
    exact by
     have hxU : spMap (ev (z ≫ toBase TF Z) U.1 hU) ≫ LogKS.chart U = z ≫ toBase TF Z :=
       FlagMod.spMap_ev (z ≫ toBase TF Z) U.2 hU
     have htan : ∀ j, IsTanAtG TF.Y.t (z ≫ toBase TF Z)
         (spMap (dualMap (ev (z ≫ toBase TF Z) U.1 hU)) ≫ v (e ⟨σ, j⟩)) := fun j => by
       have := GlobalTheory.FactorDepth.isTanAtG_map TF.Y.t (ev (z ≫ toBase TF Z) U.1 hU) (hv.1 (e ⟨σ, j⟩))
       rwa [hxU] at this
     choose B hB using fun j => GlobalTheory.FlagEmb.EigSpread.exists_lf (htan j)
     have hsum : ∀ i, ∑ j, C i j • B j = TF.X.F.vecAt k (z ≫ inc₀ TF.X Z) hk hx σ i := fun i => by
       have h := hC i
       simp only [← hB] at h
       exact (GlobalTheory.FlagEmb.EigSpread.comb_lf B (C i) _).1 h
     obtain ⟨Wm, hW⟩ := TF.X.F.uAt_split k (z ≫ inc₀ TF.X Z) hk σ
     let ρ := (Matrix.mulVecLin Wm).comp
       (FlagMod.vec (TF.X.F.M k).toMChart (z ≫ toBase TF Z) (TF.X.F.inM hk hx)).symm.toLinearMap
     have hρ : ∀ i, ρ (TF.X.F.vecAt k (z ≫ inc₀ TF.X Z) hk hx σ i) = Pi.single i 1 := fun i => by
       funext l
       have h := congrFun (congrFun hW l) i
       rw [Matrix.mul_apply] at h
       simp only [ρ, FlagMod.Frames.vecAt, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
         Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
       rw [h, Matrix.one_apply, Pi.single_apply]
     let B' : Fin (Dw.mult σ) → ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (z ≫ toBase TF Z) TF.Y.t.G := fun j => B j
     have hsum' : ∀ i, ∑ j, C i j • B' j = TF.X.F.vecAt k (z ≫ inc₀ TF.X Z) hk hx σ i := hsum
     let D : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S := Matrix.of fun j l => ρ (B' j) l
     have hCD : C * D = 1 := by
       ext i l
       have h : ρ (∑ j, C i j • B' j) = ρ (TF.X.F.vecAt k (z ≫ inc₀ TF.X Z) hk hx σ i) := congrArg ρ (hsum' i)
       set_option synthInstance.maxHeartbeats 100000 in
         rw [hρ, map_sum] at h
       have h2 := congrFun h l
       simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h2
       have h3 : (if i = l then (1 : S) else 0) = (Pi.single i (1 : S) : Fin (Dw.mult σ) → S) l := by
         rw [Pi.single_apply]
         exact if_congr eq_comm rfl rfl
       rw [Matrix.mul_apply, Matrix.one_apply, h3]
       exact h2
     exact IsUnit.of_mul_eq_one D.det (by rw [← Matrix.det_mul, hCD, Matrix.det_one])

end GlobalTheory.LogPole
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeStabiliserVacuumEigenvalueOneInertPlaceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeStabiliser_vacuum_eigenvalue_one_inert_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V v, ∀ c : ℂ, Acts (evFin F v) (om (k, 1)) (G.M.vac v) (c • G.M.vac v) → c = 1 := by
  first | exact @GlobalTheory.DblVacV.eigen_eq_one | exact GlobalTheory.DblVacV.eigen_eq_one | (intros; apply GlobalTheory.DblVacV.eigen_eq_one <;> assumption)
end

