module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.ProjectiveLattices.SpMapAlgHomId
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0870
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.IoOverLeftUnique
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import ReciprocityTheory.SemistableReduction.Bundle0025
public import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1237
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1239
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1353
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1342
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0712
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommuteOfMemZalg
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1348
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GaussianIsSchwartzFunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1333
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
public import Formalism.HarderNarasimhan.StatementPl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1335
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1307
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoeffRoots
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

namespace GlobalTheory.OneMapAll

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
  Formalism.L2.DIV GlobalTheory.FieldBC
open scoped TensorProduct

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c c' : Coeff l} {r n : ℕ}

theorem exists_coeff_roots (c : Coeff l) {z w : ℂ} (hz : ∃ m : ℕ, 0 < m ∧ z ^ m = 1) (hw : ∃ m : ℕ, 0 < m ∧ w ^ m = 1) :
    ∃ c' : Coeff l, c.F ≤ c'.F ∧ z ∈ c'.F ∧ w ∈ c'.F := by
  have hi : ∀ x : ℂ, (∃ m : ℕ, 0 < m ∧ x ^ m = 1) → IsIntegral ℚ x := by
    rintro x ⟨m, hm, h⟩
    exact IsIntegral.of_pow hm (h ▸ isIntegral_one)
  have := c.fin
  have : FiniteDimensional ℚ (IntermediateField.adjoin ℚ ({z, w} : Set ℂ)) :=
    IntermediateField.finiteDimensional_adjoin (by
      rintro x (rfl | rfl)
      · exact hi _ hz
      · exact hi _ hw)
  have hle : c.F ≤ c.F ⊔ IntermediateField.adjoin ℚ ({z, w} : Set ℂ) := le_sup_left
  have hle' : IntermediateField.adjoin ℚ ({z, w} : Set ℂ) ≤ c.F ⊔ IntermediateField.adjoin ℚ ({z, w} : Set ℂ) := le_sup_right
  exact ⟨⟨c.F ⊔ IntermediateField.adjoin ℚ ({z, w} : Set ℂ), inferInstance, fun τ a => hle (c.conj τ a), hle c.zeta_mem,
    c.le.trans hle⟩, hle, hle' (IntermediateField.subset_adjoin _ _ (by simp)),
    hle' (IntermediateField.subset_adjoin _ _ (by simp))⟩

theorem exists_coef_ext {K K' : Type} [Field K] [Field K'] (j : K →+* K') {σ : K →+* ℂ} (σ' : K' →+* ℂ)
    (hσ : ∀ a, σ' (j a) = σ a) {I : Type} [Fintype I] (lam : I → DomWeight n) {W : Type} [AddCommGroup W] [Module ℂ W]
    (c₀ : VV K lam →ₛₗ[σ] W) : ∃ c₁ : VV K' lam →ₛₗ[σ'] W, ∀ (v : VV K lam) (v' : VV K' lam),
      (v' : Pol K' I n) = MvPolynomial.map j (v : Pol K I n) → c₁ v' = c₀ v := by
  classical
  obtain ⟨p, hp⟩ := LinearMap.exists_extend (p := VV K lam) (LinearMap.id : VV K lam →ₗ[K] VV K lam)
  have hp' : ∀ v : VV K lam, p v = v := fun v => LinearMap.congr_fun hp v
  let C : Pol K' I n →ₛₗ[σ'] W :=
    { toFun := fun F => Finsupp.sum ((MvPolynomial.basisMonomials _ K').repr F)
        fun m a => σ' a • c₀ (p (MvPolynomial.monomial m 1))
      map_add' := fun F F' => by
        rw [map_add (f := _)]
        exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by simp [add_smul])
      map_smul' := fun a F => by
        rw [map_smul, Finsupp.sum_smul_index' (fun _ => by simp), Finsupp.smul_sum]
        simp [mul_smul] }
  have hC : ∀ m a, C (MvPolynomial.monomial m a) = σ' a • c₀ (p (MvPolynomial.monomial m 1)) := fun m a => by
    have e : MvPolynomial.monomial m a = a • MvPolynomial.basisMonomials _ K' m := by
      simp [MvPolynomial.smul_monomial]
    rw [e, map_smulₛₗ]
    congr 1
    show Finsupp.sum ((MvPolynomial.basisMonomials _ K').repr (MvPolynomial.basisMonomials _ K' m))
      (fun m a => σ' a • c₀ (p (MvPolynomial.monomial m 1))) = _
    rw [Module.Basis.repr_self, Finsupp.sum_single_index (by simp), map_one, one_smul]
  have key : ∀ F : Pol K I n, C (MvPolynomial.map j F) = c₀ (p F) := by
    intro F
    induction F using MvPolynomial.induction_on' with
    | monomial m a =>
      rw [MvPolynomial.map_monomial, hC, hσ, ← map_smulₛₗ, ← map_smul, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    | add F F' h h' => rw [map_add (f := _), map_add (f := _), h, h', map_add (f := _), map_add (f := _)]
  exact ⟨C.comp (VV K' lam).subtype, fun v v' h => by
    show C v' = _
    rw [h, key, hp']⟩

theorem covPin_covBC (hle : c.F ≤ c'.F) (d : DeltaDat Xo c n) {u : c'.F} (hu : u ≠ 0)
    (h : d.IsLev ∧ d.l₂.A = 1 ∧ ∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) :
    (covBC hle d u).IsLev ∧ (covBC hle d u).l₂.A = 1 ∧
      ∃ _ : StarRing (𝓞 E), IsNab (covBC hle d u).Xo₂ (covBC hle d u).c₂ (covBC hle d u).nab₂ := by
  obtain ⟨h1, h2, s, h3⟩ := h
  exact ⟨GlobalTheory.LevelCoverDatum.isLev_smul (ddBC hle d) (GlobalTheory.FieldBCModel.isLev_ddBC hle d h1) u hu, h2, s,
    GlobalTheory.FieldBCModel.isNab_nabBC (le_covCoeff hle d) d.nab₂ h3⟩

theorem phiHat_covBC (hle : c.F ≤ c'.F) (d : DeltaDat Xo c n) (u : c'.F) (φ : (Fin n → LevQc Dw d.l₂) → c.F)
    (w : c.F) (q : Fin n → LevQ Dw d.l₂) (h : d.eF w = phiHat d.c₂ (fun x => d.eF (φ x)) q) :
    (covBC hle d u).eF (incF c c' hle w) =
      phiHat (covBC hle d u).c₂ (fun x => (covBC hle d u).eF (incF c c' hle (φ x))) q := by
  have e := congrArg (incF d.c₂ (covCoeff hle d) (le_covCoeff hle d)) h
  refine Eq.trans (Subtype.ext rfl) (e.trans ?_)
  unfold phiHat
  have hz : zetaM (covCoeff hle d) = incF d.c₂ (covCoeff hle d) (le_covCoeff hle d) (zetaM d.c₂) := by
    unfold zetaM; rw [map_pow]; rfl
  refine (AddMonoidHom.map_finsum_of_injective
    (incF d.c₂ (covCoeff hle d) (le_covCoeff hle d)).toAddMonoidHom (RingHom.injective _) _).trans ?_
  refine finsum_congr fun x => ?_
  show incF d.c₂ (covCoeff hle d) (le_covCoeff hle d) (_ * _) = _
  rw [map_mul, map_zpow₀, ← hz]
  rfl

theorem epIs_map (hle : c.F ≤ c'.F) {bad : ℕ} {B : Ideal (𝓞 E) → c.F} {epF : Submodule (𝓞 E) (Fin n → E) → c.F}
    (h : EpIs (Dw := Dw) c bad B epF) :
    EpIs (Dw := Dw) c' bad (fun I => incF c c' hle (B I)) (fun L => incF c c' hle (epF L)) := by
  intro L cc h1 h2 h3 h4 h5
  obtain ⟨q, a, b, e⟩ := h L cc h1 h2 h3 h4 h5
  exact ⟨q, a, b, by simp only [e, map_mul, map_inv₀, map_ratCast]⟩

theorem isThClsD_covBC_one (hle : c.F ≤ c'.F) (d : DeltaDat Xo c n) {u : c'.F} (hu : u = 1) {Cl : Type} [Fintype Cl]
    (w : Cl → (Fin n → LevQ Dw d.l₂) → c.F) (La : Cl → GenLat E n) (Nc gam : Cl → ℕ) (vol : c.F) (ep : Cl → c.F)
    {Vs : Type} [AddCommGroup Vs] [Module c.F Vs] (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F)
    {Vs' : Type} [AddCommGroup Vs'] [Module c'.F Vs'] (io' : Vs' →ₗ[c'.F] MvPolynomial (LtN Dw n) c'.F)
    (x : Cl → Vs) (x' : Cl → Vs') (hx : ∀ k, io' (x' k) = MvPolynomial.map (incF c c' hle) (io (x k)))
    (hd : d.cδ ∈ sec d.Xo₂ d.c₂ 0 0) {a : (E →+* ℂ) × ℕ → ℕ} {m : ℕ} {f : Rul Xo c} (hf : f ∈ sec Xo c a m)
    (h : IsThClsD Xo c d w La Nc gam vol ep io x f) :
    IsThClsD Xo c' (covBC hle d u) (fun k q => incF c c' hle (w k q)) La Nc gam (incF c c' hle vol)
      (fun k => incF c c' hle (ep k)) io' x' (rulBC hle f) := by
  subst hu
  have h' := (GlobalTheory.ClassSumFieldChange.isThClsD_ddBC_iff E H Dw l Xo c c' hle n d Cl w La Nc gam vol ep Vs io Vs' io' x x'
    hx hd a m f hf).2 h
  intro k _ _ _ i hk y y₂ hy
  obtain ⟨vc, h1, h2⟩ := @h' k _ _ _ i hk y y₂ hy
  refine ⟨vc, h1, h2.trans ?_⟩
  have e : (covBC hle d 1).cδ = (ddBC hle d).cδ := one_smul (covCoeff hle d).F (rulBC (le_covCoeff hle d) d.cδ)
  rw [e]
  rfl

theorem isBC_rulBC_trans {c₀ : Coeff l} (h₀ : c₀.F ≤ c.F) (hle : c.F ≤ c'.F) (h₁ : c₀.F ≤ c'.F)
    {a : (E →+* ℂ) × ℕ → ℕ} {k m : ℕ} {f : Rul Xo c} (hf : f ∈ sec Xo c a k) {as : Fin m → c.F} {fs : Fin m → Rul Xo c₀}
    (h : IsBC h₀ f as fs) : IsBC h₁ (rulBC hle f) (fun i => incF c c' hle (as i)) fs := by
  intro S _ _ _ hS y
  letI := resAlg hle S
  rw [GlobalTheory.FieldBCModel.evR_rulBC hle hf.1 (fun _ => rfl) y, h S (fun a => hS a) _]
  rfl

end Gen

section Forms

open _root_.Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.MainNotions Formalism.IndefR.Links

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
  {K' : Type} [Field K'] {σ' : K' →+* ℂ} (t : T0) {Cl : Type} (h : Cl → GA D (Vc D i))
  (c0' : VsV D i K' →ₛₗ[σ'] (R.cV i).W)

theorem adForms_ext {Gp Γ W I : Type} [Group Gp] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] {ι : Γ →* Gp}
    {ρ : Γ →* Module.End ℂ W} {J J' : Subgroup Gp} {χ : J →* ℂˣ} {F F' : Gp → W} (hF : F ∈ Bridge.AdForms ι ρ J χ)
    (hF' : F' ∈ Bridge.AdForms ι ρ J χ) (hJ : J' ≤ J) {y : I → Gp} (hr : Bridge.IsReps ι J' y)
    (h : ∀ k, F (y k) = F' (y k)) : F = F' := by
  funext g
  obtain ⟨k, ⟨γ, κ, rfl⟩, -⟩ := hr g
  have h1 := hF γ (y k) ⟨κ, hJ κ.2⟩
  have h2 := hF' γ (y k) ⟨κ, hJ κ.2⟩
  rw [h k] at h1
  exact h1.trans h2.symm

theorem place_unique (hV : R.models_HV) {J' : Subgroup (Bridge.Gf (Vc D i))} (hJ : J' ≤ levJ R i t)
    (hr : Bridge.IsReps (Bridge.ratF (Vc D i)) J' (fun k => fin _ (h k))) {y y' : (R.HV i t).H} {x : Cl → VsV D i K'}
    (hy : Place R i t h c0' y x) (hy' : Place R i t h c0' y' x) : y = y' := by
  exact (hV i t).1 (adForms_ext ((hV i t).2.1.le (LinearMap.mem_range_self (R.HV i t).e y))
    ((hV i t).2.1.le (LinearMap.mem_range_self (R.HV i t).e y')) hJ hr fun k => (hy k).trans (hy' k).symm)


open Classical in
def thAdOf (v₀ : (R.MW i (sg0 D A)).Vec) (x : Cl → VsV D i K') : AutQ (Wc D i) → ℂ :=
  if hx : ∃ y, Place R i t h c0' y x then onQ (Wc D i) (R.thF i t hx.choose v₀) else 0

theorem thAdIs_thAdOf (hV : R.models_HV) {J' : Subgroup (Bridge.Gf (Vc D i))} (hJ : J' ≤ levJ R i t)
    (hr : Bridge.IsReps (Bridge.ratF (Vc D i)) J' (fun k => fin _ (h k))) (v₀ : (R.MW i (sg0 D A)).Vec) :
    ThAdIs R i t h c0' v₀ (thAdOf R i t h c0' v₀) := by
  intro y x hy
  have hx : ∃ y, Place R i t h c0' y x := ⟨y, hy⟩
  have e := place_unique R i t h c0' hV hJ hr hx.choose_spec hy
  exact (dif_pos hx).trans (congrArg (fun y => onQ (Wc D i) (R.thF i t y v₀)) e)

end Forms

end GlobalTheory.OneMapAll
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqIsoSpecComp
section
set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.HSChoice.EtaleSection

theorem exists_eq_isoSpec_comp {k : Type} [CommRing k] {X : Scheme.{0}} [IsAffine X] (g : X ⟶ Spec (.of k)) :
    letI := algebraΓOfHom g
    ∃ a : CommRingCat.of k ⟶ Γ(X, ⊤), a.hom = algebraMap k Γ(X, ⊤) ∧ g = X.isoSpec.hom ≫ Spec.map a := by
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ g.appTop, rfl, ?_⟩
  rw [Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom, ← Scheme.toSpecΓ_naturality, Category.assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

theorem natCard_subPts {k : Type} [Field k] (S : LinSys k) (I : S.Y.IdealSheafData) (hI : S.IsFiniteSub I)
    (Ω : Type) [Field Ω] [Algebra k Ω] :
    letI := algebraΓOfHom (I.subschemeι ≫ S.str)
    Nat.card (S.subPts I Ω) = Nat.card (Γ(I.subscheme, ⊤) →ₐ[k] Ω) := by
  letI := algebraΓOfHom (I.subschemeι ≫ S.str)
  haveI : IsFinite (I.subschemeι ≫ S.str) := hI
  haveI : IsAffine I.subscheme := isAffine_of_isAffineHom (I.subschemeι ≫ S.str)
  obtain ⟨a, ha, he⟩ := exists_eq_isoSpec_comp (I.subschemeι ≫ S.str)
  have e1 : Nat.card (S.subPts I Ω) =
      Nat.card {z : Sp Ω ⟶ I.subscheme // z ≫ I.subschemeι ≫ S.str = spMap (algebraMap k Ω)} := by
    refine (Nat.card_congr (Equiv.ofBijective (fun z => (⟨⟨z.1 ≫ I.subschemeι, by rw [Category.assoc]; exact z.2⟩,
      z.1, rfl⟩ : S.subPts I Ω)) ⟨?_, ?_⟩)).symm
    · intro z z' h
      apply Subtype.ext
      have h0 : z.1 ≫ I.subschemeι = z'.1 ≫ I.subschemeι := congrArg (fun x : S.subPts I Ω => x.1.1) h
      exact (cancel_mono I.subschemeι).1 h0
    · rintro ⟨x, z, hz⟩
      refine ⟨⟨z, ?_⟩, ?_⟩
      · rw [← Category.assoc, hz]
        exact x.2
      · apply Subtype.ext
        apply Subtype.ext
        exact hz
  have hmk : ∀ φ : Γ(I.subscheme, ⊤) →ₐ[k] Ω,
      (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ I.subscheme.isoSpec.inv) ≫ I.subschemeι ≫ S.str =
        spMap (algebraMap k Ω) := by
    intro φ
    rw [he, Category.assoc, Iso.inv_hom_id_assoc, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    ext r
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    rw [ha]
    exact φ.commutes r
  have e2 : Nat.card {z : Sp Ω ⟶ I.subscheme // z ≫ I.subschemeι ≫ S.str = spMap (algebraMap k Ω)} =
      Nat.card (Γ(I.subscheme, ⊤) →ₐ[k] Ω) := by
    refine (Nat.card_congr (Equiv.ofBijective (fun φ : Γ(I.subscheme, ⊤) →ₐ[k] Ω =>
      (⟨Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ I.subscheme.isoSpec.inv, hmk φ⟩ :
        {z : Sp Ω ⟶ I.subscheme // z ≫ I.subschemeι ≫ S.str = spMap (algebraMap k Ω)})) ⟨?_, ?_⟩)).symm
    · intro φ ψ h
      simp only [Subtype.mk.injEq, cancel_mono] at h
      have h2 := Spec.map_injective h
      ext r
      exact congrArg (fun f => f.hom r) h2
    · rintro ⟨z, hz⟩
      have hψ : Spec.map (Spec.preimage (z ≫ I.subscheme.isoSpec.hom)) = z ≫ I.subscheme.isoSpec.hom :=
        Spec.map_preimage _
      have hc : a ≫ Spec.preimage (z ≫ I.subscheme.isoSpec.hom) = CommRingCat.ofHom (algebraMap k Ω) := by
        apply Spec.map_injective
        rw [Spec.map_comp, hψ, Category.assoc, ← he]
        exact hz
      refine ⟨AlgHom.mk (Spec.preimage (z ≫ I.subscheme.isoSpec.hom)).hom (fun r => ?_), ?_⟩
      · have h3 := congrArg (fun f => f.hom r) hc
        simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom, ha] at h3
        exact h3
      · apply Subtype.ext
        rw [Iso.comp_inv_eq]
        exact hψ
  rw [e1, e2]

theorem etale_of_algebraEtale {k : Type} [Field k] (S : LinSys k) (I : S.Y.IdealSheafData) (hI : S.IsFiniteSub I) :
    letI := algebraΓOfHom (I.subschemeι ≫ S.str)
    Algebra.Etale k Γ(I.subscheme, ⊤) → Etale (I.subschemeι ≫ S.str) := by
  letI := algebraΓOfHom (I.subschemeι ≫ S.str)
  intro h
  haveI : IsFinite (I.subschemeι ≫ S.str) := hI
  haveI : IsAffine I.subscheme := isAffine_of_isAffineHom (I.subschemeι ≫ S.str)
  obtain ⟨a, ha, he⟩ := exists_eq_isoSpec_comp (I.subschemeι ≫ S.str)
  have h2 : Etale (Spec.map a) := by
    refine HasRingHomProperty.Spec_iff.mpr ?_
    rw [ha]
    exact (RingHom.etale_algebraMap (R := k) (S := Γ(I.subscheme, ⊤))).mpr h
  rw [he]
  infer_instance

theorem finite_finrank {F : Type} [Field F] [NumberField F] (T : Tuple F) (hT : T.IsGeometric) (E : Type) [Field E]
    [Algebra F E] (s : Fin T.D → Fin T.N → E)
    (hfin : ((T.linSection E s).support : Set (T.toLinSys.baseChange E).Y).Finite) :
    (T.toLinSys.baseChange E).IsFiniteSub (T.linSection E s) ∧
    (letI := algebraΓOfHom ((T.linSection E s).subschemeι ≫ (T.toLinSys.baseChange E).str)
    Module.Finite E Γ((T.linSection E s).subscheme, ⊤) ∧
      (Module.finrank E Γ((T.linSection E s).subscheme, ⊤) : ℤ) = T.del) := by
  have hv : (T.toLinSys.baseChange E).IsVariety := hT.alg.variety.baseChange E
  have H := GlobalTheory.ProperCut.topSelf_eq_length_of_smooth (T.toLinSys.baseChange E).str hv.smooth hv.proj
    (T.toLinSys.baseChange E).isLB (fun i => (T.toLinSys.baseChange E).comb (s i)) hfin
  have hdel : (T.toLinSys.baseChange E).del = T.del :=
    GlobalTheory.FieldChangeInter.del_baseChange F E T.toLinSys hT.alg.variety.proj
  refine ⟨H.1, ?_⟩
  refine ⟨H.2.2.2.2.1, ?_⟩
  rw [← hdel]
  exact H.2.2.2.2.2.symm

private lemma isHomogeneous_join_C_X {K : Type} [CommRing K] {D N : ℕ} (s : Fin D → Fin N → K) (v : Fin (D + 1) × Fin N) :
    (join (fun i j => (C (s i j) : MvPolynomial (Fin 1 × Fin N) K)) (fun j => X ((0 : Fin 1), j)) v).IsHomogeneous
      (if v.1 = Fin.last D then 1 else 0) := by
  obtain ⟨i, j⟩ := v
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
  · simpa [join, Fin.castSucc_ne_last] using isHomogeneous_C (Fin 1 × Fin N) (s i j)
  · simpa [join] using isHomogeneous_X K ((0 : Fin 1), j)

theorem isHomogeneous_spec {F K : Type} [Field F] [Field K] [Algebra F K] {D N δ : ℕ} (s : Fin D → Fin N → K)
    (f : MvPolynomial (Fin (D + 1) × Fin N) F) (hf : IsMultiHomogeneous (fun _ => δ) f) :
    (spec s f).IsHomogeneous δ := by
  classical
  unfold spec
  set_option synthInstance.maxHeartbeats 100000 in
    rw [f.as_sum, map_sum]
  apply IsHomogeneous.sum
  intro m hm
  have hprod : (m.prod fun v e =>
      (join (fun i j => (C (s i j) : MvPolynomial (Fin 1 × Fin N) K)) (fun j => X ((0 : Fin 1), j)) v) ^ e).IsHomogeneous
      (∑ v ∈ m.support, (if v.1 = Fin.last D then 1 else 0) * m v) :=
    IsHomogeneous.prod _ _ _ fun v _ => (isHomogeneous_join_C_X s v).pow (m v)
  have hdeg : ∑ v ∈ m.support, (if v.1 = Fin.last D then 1 else 0) * m v = δ := by
    rw [Finset.sum_subset (Finset.subset_univ _) (fun v _ hv => by simp [Finsupp.notMem_support_iff.1 hv])]
    rw [Fintype.sum_prod_type, Finset.sum_eq_single (Fin.last D)]
    · simpa using hf m hm (Fin.last D)
    · intro i _ hi
      simp [hi]
    · simp
  have h2 := (isHomogeneous_C (Fin 1 × Fin N) (algebraMap F K (AddMonoidAlgebra.coeff f m))).mul hprod
  rw [zero_add, hdeg] at h2
  rw [aeval_monomial, MvPolynomial.algebraMap_apply]
  exact h2

private lemma eval_join_C_X_eq_join {K : Type} [CommRing K] {D N : ℕ} (s : Fin D → Fin N → K) (ξ : Fin N → K)
    (v : Fin (D + 1) × Fin N) :
    eval (fun p : Fin 1 × Fin N => ξ p.2)
      (join (fun i j => (C (s i j) : MvPolynomial (Fin 1 × Fin N) K)) (fun j => X ((0 : Fin 1), j)) v) = join s ξ v := by
  obtain ⟨i, j⟩ := v
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
  · simp [join]
  · simp [join]

theorem eval_spec {F K : Type} [CommRing F] [CommRing K] [Algebra F K] {D N : ℕ} (s : Fin D → Fin N → K)
    (f : MvPolynomial (Fin (D + 1) × Fin N) F) (ξ : Fin N → K) :
    eval (fun p => ξ p.2) (spec s f) = aeval (join s ξ) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [spec, MvPolynomial.algebraMap_apply]
  | add p q hp hq =>
    simp only [spec, map_add (f := _)] at hp hq ⊢
    rw [hp, hq]
  | mul_X p v hp =>
    simp only [spec, map_mul, aeval_X] at hp ⊢
    rw [hp, eval_join_C_X_eq_join]

end GlobalTheory.HSChoice.EtaleSection
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExpand
section
noncomputable section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.CuspRep

namespace GlobalTheory.LeviGL.ZGood

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem zalg_commute {z z' : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) (hz' : z' ∈ Zalg E a) : Commute z z' := by
  first
  | exact @_root_.GlobalTheory.QuantumMinorCharts.commute_of_mem_Zalg
  | exact _root_.GlobalTheory.QuantumMinorCharts.commute_of_mem_Zalg
  | (apply _root_.GlobalTheory.QuantumMinorCharts.commute_of_mem_Zalg <;> assumption)
  | (intros; apply _root_.GlobalTheory.QuantumMinorCharts.commute_of_mem_Zalg <;> assumption)
  | (intros; apply @_root_.GlobalTheory.QuantumMinorCharts.commute_of_mem_Zalg <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.QuantumMinorCharts.commute_of_mem_Zalg ..)

end GlobalTheory.LeviGL.ZGood

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaussianDerivative
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.ThK.EvAt0
open GlobalTheory.ThK.EvAt0.PolD

namespace GlobalTheory.ThK.EvAt0.GaussForm

theorem exists_schwartz_gauss_form {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : LinearMap.BilinForm ℝ E) (hs : ∀ p p', Q p p' = Q p' p) (hp : ∀ p, p ≠ 0 → 0 < Q p p) :
    ∃ G : SchwartzMap E ℂ, ∀ s, G s = Complex.exp (-(Real.pi : ℂ) * (Q s s : ℂ)) ∧
      ∀ v, fderiv ℝ (⇑G) s v = -(2 * (Real.pi : ℂ)) * (Q s v : ℂ) * G s := by
  let B : E →L[ℝ] E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] _).toLinearMap ∘ₗ ((-Real.pi) • Q))
  have hB : ∀ x y, B x y = -Real.pi * Q x y := fun x y => rfl
  obtain ⟨G, hG⟩ := GlobalTheory.GaussSchwartz.exists_schwartz_exp_diag B (fun x hx => by
    rw [hB]
    have := mul_pos Real.pi_pos (hp x hx)
    linarith)
  refine ⟨G, fun s => ⟨?_, fun v => ?_⟩⟩
  · rw [hG, hB]; push_cast; rfl
  · have hfun : (⇑G) = fun x => Complex.ofRealCLM (Real.exp (B x x)) := funext fun x => hG x
    have h1 := (B.hasFDerivAt (x := s)).clm_apply (hasFDerivAt_id s)
    have h2 := Complex.ofRealCLM.hasFDerivAt.comp s h1.exp
    have h3 := congrArg (fun f => fderiv ℝ f s) hfun
    rw [h3.trans h2.fderiv, hG]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.id_apply, id, Complex.ofRealCLM_apply, hB, smul_eq_mul,
      hs v s]
    push_cast
    ring

end GlobalTheory.ThK.EvAt0.GaussForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftSectionsZeroSchemeRegularSequenceLineBStatement
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_sections_zeroScheme_regularSequence_lineBundle : ∀ (k : Type) [Field k] (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (GlobalTheory.strHom k (X := Y)) → ∀ (p : Y ⟶ Sp k) (M L : LB Y), M.IsLB → ∀ (hL : L.IsLB) (d : ℕ) (t : Fin d → L.Sec) (l : ℤ), RegSeq hL (GlobalTheory.LB.toMod M) (List.ofFn t) → VanishFrom L (GlobalTheory.LB.toMod M) 0 → (d : ℤ) ≤ l → ∀ (W : Y → Y.Opens) (b : ∀ y, Vanishing.H0 p (tw M L l) (W y)), (∀ y, y ∈ W y) → (∀ y z, VanishesTo (cutIdeal hL t) 1 (Vanishing.H0.restr inf_le_left (b y) - Vanishing.H0.restr inf_le_right (b z) : Vanishing.H0 p (tw M L l) (W y ⊓ W z))) → ∃ σ : Vanishing.H0 p (tw M L l) ⊤, ∀ y, VanishesTo (cutIdeal hL t) 1 (Vanishing.H0.restr le_top σ - b y) := by
  first | exact @GlobalTheory.HSCore.exists_glue_mod_regSeq | exact GlobalTheory.HSCore.exists_glue_mod_regSeq | (intros; apply GlobalTheory.HSCore.exists_glue_mod_regSeq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticGroupMatrixOfPreservesPhaseSpaceStatement
section
open scoped SchwartzMap Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symplecticGroup_matrix_of_preserves_phaseSpaceForm : ∀ (l : Type) [Fintype l] [DecidableEq l] (ψ : (l ⊕ l → ℝ) →ₗ[ℝ] (l ⊕ l → ℝ)),
    (∀ w w', GlobalTheory.RealWeil.sympl (ψ w) (ψ w') = GlobalTheory.RealWeil.sympl w w') →
    ∃ M : Matrix.symplecticGroup l ℝ, ∀ w, (M : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w = ψ w := by
  first | exact @GlobalTheory.exists_symplecticGroup_of_sympl | exact GlobalTheory.exists_symplecticGroup_of_sympl | (intros; apply GlobalTheory.exists_symplecticGroup_of_sympl <;> assumption)
end

