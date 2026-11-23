module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0579
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolFanExtensionConeTransfer
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0526
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1672
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0456
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0447
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGenericFrameTranscendentalSpecialisingTwo
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenFrame

open Matrix ReciprocityTheory.ChartRestriction.G.PullbackSections

def mixM {K R : Type} [CommRing K] [CommRing R] {n : ℕ} (κ : K →+* R) (u : R) (A : Matrix (Fin n) (Fin n) K) :
    Matrix (Fin n) (Fin n) R := (1 - u) • (1 : Matrix (Fin n) (Fin n) R) + u • A.map κ

theorem mixM_map {K R R' : Type} [CommRing K] [CommRing R] [CommRing R'] {n : ℕ} (κ : K →+* R) (u : R)
    (A : Matrix (Fin n) (Fin n) K) (ψ : R →+* R') : (mixM κ u A).map ψ = mixM (ψ.comp κ) (ψ u) A := by
  ext a b
  by_cases h : a = b
  · subst h; simp [mixM]
  · simp [mixM, Matrix.one_apply_ne h]

def detPoly {K : Type} [CommRing K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K) : Polynomial K :=
  (mixM Polynomial.C Polynomial.X A).det

theorem det_mixM {K R : Type} [CommRing K] [CommRing R] {n : ℕ} (κ : K →+* R) (u : R) (A : Matrix (Fin n) (Fin n) K) :
    (mixM κ u A).det = (detPoly A).eval₂ κ u := by
  rw [detPoly, ← Polynomial.coe_eval₂RingHom, RingHom.map_det, RingHom.mapMatrix_apply, mixM_map]
  congr 2
  · ext a; simp
  · simp

theorem mixM_zero {K : Type} [CommRing K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K) : mixM (RingHom.id K) 0 A = 1 := by
  simp [mixM]

theorem mixM_one {K : Type} [CommRing K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K) : mixM (RingHom.id K) 1 A = A := by
  simp [mixM]

theorem detPoly_ne_zero {K : Type} [Field K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K) : detPoly A ≠ 0 := by
  intro h
  have := det_mixM (RingHom.id K) 0 A
  rw [h, mixM_zero, Polynomial.eval₂_zero, det_one] at this
  exact one_ne_zero this

end GlobalTheory.GenFrame

namespace GlobalTheory.GenFrame

open Matrix _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.BasicNotions GlobalTheory.CxPts GlobalTheory.LieMet

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem exists_co_eq {R : Type} [CommRing R] {φ : c.F →+* R} {x : Sp R ⟶ Z.X} (f : EigFrame Z φ x)
    (T : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) R) (hT : ∀ τ, IsUnit (T τ).det) :
    ∃ g : EigFrame Z φ x, ∀ τ, f.co g τ = T τ := by
  have hsum : ∀ τ (a : Fin (Dw.mult τ) → R),
      ∑ i, a i • ∑ j, T τ j i • f.vec τ j = ∑ j, (T τ *ᵥ a) j • f.vec τ j := by
    intro τ a
    simp only [Finset.smul_sum, smul_smul, mulVec, dotProduct, Finset.sum_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by rw [mul_comm]
  let g : EigFrame Z φ x := EigFrame.ofVec (fun τ i => ∑ j, T τ j i • f.vec τ j)
    (fun τ i a => by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, f.act_vec, Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _)
    (fun τ w hw => by
      obtain ⟨b, hb, hbu⟩ := f.existsUnique_sum τ w hw
      refine ⟨(T τ)⁻¹ *ᵥ b, ?_, fun a ha => ?_⟩
      · show w = ∑ i, ((T τ)⁻¹ *ᵥ b) i • ∑ j, T τ j i • f.vec τ j
        rw [hsum, mulVec_mulVec, mul_nonsing_inv _ (hT τ), one_mulVec]
        exact hb
      · have h1 : T τ *ᵥ a = b := hbu _ (ha.trans (hsum τ a))
        rw [← h1, mulVec_mulVec, nonsing_inv_mul _ (hT τ), one_mulVec])
  refine ⟨g, fun τ => EigFrame.co_eq fun i => ?_⟩
  exact (isComb_iff (f.vec τ) (fun a => T τ a i) (∑ j, T τ j i • f.vec τ j)).2 rfl

theorem co_eq_one {R : Type} [CommRing R] {φ : c.F →+* R} {x : Sp R ⟶ Z.X} {f₀ f₁ f₂ : EigFrame Z φ x}
    {τ : E →+* ℂ} (h : f₀.co f₁ τ = f₀.co f₂ τ) : f₁.co f₂ τ = 1 := by
  rw [← f₁.co_mul f₀ f₂ τ, ← h, f₁.co_mul f₀ f₁ τ, f₁.co_self τ]

theorem tri_of_co_eq_one {R R' : Type} [CommRing R] [CommRing R'] {φ : c.F →+* R} {x : Sp R ⟶ Z.X}
    {φ' : c.F →+* R'} {x' : Sp R' ⟶ Z.X} {f : EigFrame Z φ x} {ψ : R →+* R'} {f' g : EigFrame Z φ' x'}
    (hf : (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v f embτ basisIdx) ψ f') (hφ : φ' = ψ.comp φ) (hx : x' = spMap ψ ≫ x) (h : ∀ τ, f'.co g τ = 1) : f.Tri ψ g 1 := by
  refine ⟨hx, hφ, fun τ i => ⟨fun a => f'.co g τ a i, by simp [h], fun k hk => by
    simp [h, Matrix.one_apply_ne hk.ne'], ?_⟩⟩
  rw [← funext (hf τ)]
  exact f'.co_spec g τ i

theorem isMap_id {R : Type} [CommRing R] {φ : c.F →+* R} {x : Sp R ⟶ Z.X} (f : EigFrame Z φ x) :
    (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v f embτ basisIdx) (RingHom.id R) f := fun τ i => by
  have h1 : spMap (dualMap (RingHom.id R)) = 𝟙 _ := by
    rw [← Spec.map_id]
    congr 1
    ext r <;> simp [dualMap]
  rw [h1, Category.id_comp]

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

end GlobalTheory.GenFrame


open Matrix in
theorem GlobalTheory.GenFrame.exists_generic_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (K : Type) [Field K] (χ : c.F →+* K) (x : Sp K ⟶ Z.X) (g g' : EigFrame Z χ x) (L : Type) [Field L] (ι : K →+* L) (s : L), (∀ P : Polynomial K, P.eval₂ ι s = 0 → P = 0) → ∀ (xL : Sp L ⟶ Z.X), xL = spMap ι ≫ x → ∃ gL : EigFrame Z (ι.comp χ) xL, ∀ (V : Type) [CommRing V] [IsLocalRing V] (ν : V →+* L) (ιV : K →+* V) (r : V →+* K) (sV : V), ν.comp ιV = ι → r.comp ιV = RingHom.id K → RingHom.ker r = IsLocalRing.maximalIdeal V → ν sV = s → (r sV = 0 → ∃ (gV : EigFrame Z (ιV.comp χ) (spMap ιV ≫ x)) (tL : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Lˣ) (tk : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ), gV.Tri ν gL tL ∧ gV.Tri r g tk) ∧ (r sV = 1 → ∃ (gV : EigFrame Z (ιV.comp χ) (spMap ιV ≫ x)) (tL : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Lˣ) (tk : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ), gV.Tri ν gL tL ∧ gV.Tri r g' tk) := by
  intro E _ _ _ H Dw l Xo c O _ β Z K _ χ x g g' L _ ι s hs xL hxL
  have hP : ∀ τ, (GlobalTheory.GenFrame.detPoly (g.co g' τ)).eval₂ ι s ≠ 0 := fun τ h =>
    GlobalTheory.GenFrame.detPoly_ne_zero _ (hs _ h)
  obtain ⟨gB, hgB⟩ := g.exists_isMap ι (φ' := ι.comp χ) rfl hxL
  obtain ⟨gL, hgL⟩ := GlobalTheory.GenFrame.exists_co_eq gB (fun τ => GlobalTheory.GenFrame.mixM ι s (g.co g' τ)) fun τ => by
    rw [GlobalTheory.GenFrame.det_mixM]
    exact (hP τ).isUnit
  refine ⟨gL, fun V _ _ ν ιV r sV hνι hrι hker hνs => ?_⟩
  obtain ⟨gVB, hgVB⟩ := g.exists_isMap ιV (φ' := ιV.comp χ) (x' := spMap ιV ≫ x) rfl rfl
  have hxν : xL = spMap ν ≫ spMap ιV ≫ x := by
    rw [hxL, ← Category.assoc, GlobalTheory.GenFrame.spMap_comp, hνι]
  have hxr : x = spMap r ≫ spMap ιV ≫ x := by
    rw [← Category.assoc, GlobalTheory.GenFrame.spMap_comp, hrι]
    exact (Category.id_comp x).symm.trans (congrArg (· ≫ x) (Spec.map_id _).symm)
  have hφν : ι.comp χ = ν.comp (ιV.comp χ) := by rw [← RingHom.comp_assoc, hνι]
  have hφr : χ = r.comp (ιV.comp χ) := by rw [← RingHom.comp_assoc, hrι]; rfl
  have hBν : gVB.IsMap ν gB := fun τ i => by
    rw [hgB τ i, hgVB τ i, GlobalTheory.GradedPieces.dual_comp, hνι]
  have hBr : gVB.IsMap r g := fun τ i => by
    rw [hgVB τ i, GlobalTheory.GradedPieces.dual_comp, hrι]
    exact (GlobalTheory.GenFrame.isMap_id g τ i)

  have main : ∀ (hu : ∀ τ, IsUnit (GlobalTheory.GenFrame.mixM ιV sV (g.co g' τ)).det),
      ∃ gV : EigFrame Z (ιV.comp χ) (spMap ιV ≫ x), gV.Tri ν gL 1 ∧
        ∃ gVr : EigFrame Z χ x, (_root_.GlobalTheory.ShFam.EigFrame.IsMap gV) r gVr ∧ ∀ τ, g.co gVr τ = GlobalTheory.GenFrame.mixM (RingHom.id K) (r sV) (g.co g' τ) := by
    intro hu
    obtain ⟨gV, hgV⟩ := GlobalTheory.GenFrame.exists_co_eq gVB (fun τ => GlobalTheory.GenFrame.mixM ιV sV (g.co g' τ)) hu
    obtain ⟨gVν, hgVν⟩ := gV.exists_isMap ν hφν hxν
    obtain ⟨gVr, hgVr⟩ := gV.exists_isMap r hφr hxr
    refine ⟨gV, GlobalTheory.GenFrame.tri_of_co_eq_one hgVν hφν hxν fun τ => GlobalTheory.GenFrame.co_eq_one (f₀ := gB) ?_, gVr, hgVr,
      fun τ => ?_⟩
    · rw [hBν.co τ hgVν hxν, hgV, hgL, GlobalTheory.GenFrame.mixM_map, hνι, hνs]
    · rw [hBr.co τ hgVr hxr, hgV, GlobalTheory.GenFrame.mixM_map, hrι]
  have hunit : (∀ τ, r (GlobalTheory.GenFrame.mixM ιV sV (g.co g' τ)).det ≠ 0) →
      ∀ τ, IsUnit (GlobalTheory.GenFrame.mixM ιV sV (g.co g' τ)).det := fun h τ => by
    rw [← IsLocalRing.notMem_maximalIdeal, ← hker, RingHom.mem_ker]
    exact h τ
  have hr : ∀ τ, r (GlobalTheory.GenFrame.mixM ιV sV (g.co g' τ)).det =
      (GlobalTheory.GenFrame.mixM (RingHom.id K) (r sV) (g.co g' τ)).det := fun τ => by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, GlobalTheory.GenFrame.mixM_map, hrι]
  refine ⟨fun h0 => ?_, fun h1 => ?_⟩
  · obtain ⟨gV, hL, gVr, hgVr, hco⟩ := main (hunit fun τ => by
      rw [hr, h0, GlobalTheory.GenFrame.mixM_zero, det_one]; exact one_ne_zero)
    refine ⟨gV, 1, 1, hL, GlobalTheory.GenFrame.tri_of_co_eq_one hgVr hφr hxr fun τ => GlobalTheory.GenFrame.co_eq_one (f₀ := g) ?_⟩
    rw [hco, h0, GlobalTheory.GenFrame.mixM_zero, g.co_self]
  · obtain ⟨gV, hL, gVr, hgVr, hco⟩ := main (hunit fun τ => by
      rw [hr, h1, GlobalTheory.GenFrame.mixM_one]; exact (g.isUnit_det_co g' τ).ne_zero)
    refine ⟨gV, 1, 1, hL, GlobalTheory.GenFrame.tri_of_co_eq_one hgVr hφr hxr fun τ => GlobalTheory.GenFrame.co_eq_one (f₀ := g) ?_⟩
    rw [hco, h1, GlobalTheory.GenFrame.mixM_one]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicChartOfExpChartGenericFibre
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieBase

open GlobalTheory.Points Filter Topology

section Transfer

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) {X : Var F} {j : X.X ⟶ gen Z}
  (hj : j ≫ genStr Z ≫ spMap e.toRingHom = X.str)

theorem isOpenEmbedding_cxOf [IsOpenImmersion j] : IsOpenEmbedding (cxOf e σ hj) := by
  have hc : Continuous (cxOf e σ hj) :=
    continuous_induced_rng.2 ((continuous_comp (C := ℂ) j).comp continuous_subtype_val)
  refine ⟨IsEmbedding.of_comp hc continuous_subtype_val
    (((isOpenEmbedding_comp (C := ℂ) j).isEmbedding).comp IsEmbedding.subtypeVal), ?_⟩
  have hr : Set.range (cxOf e σ hj) = Subtype.val ⁻¹' Set.range fun x : Sp ℂ ⟶ X.X => x ≫ j := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.1, rfl⟩
    · rintro ⟨x, hx⟩
      replace hx : x ≫ j = y.1 := hx
      refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
      rw [← hj, ← Category.assoc, hx, ← Category.assoc, y.2, ← Spec.map_comp]
      rfl
  rw [hr]
  exact (isOpenEmbedding_comp (C := ℂ) j).isOpen_range.preimage continuous_subtype_val

variable [IsOpenImmersion j]

theorem le_preimage_cxOf (W : X.X.Opens) {z : CxPts X.str (σ.comp e.toRingHom)}
    (hz : z ∈ ptsIn X.str (σ.comp e.toRingHom) W) : ⊤ ≤ (cxOf e σ hj z).1 ⁻¹ᵁ (j ''ᵁ W) :=
  le_preimage_comp z.1 j (j.preimage_image_eq W).ge hz

theorem ev_eq_valAt'_cxOf (W : X.X.Opens) (g : Γ(X.X, W)) {z : CxPts X.str (σ.comp e.toRingHom)}
    (hz : z ∈ ptsIn X.str (σ.comp e.toRingHom) W) :
    ev X.str (σ.comp e.toRingHom) W g z = valAt' (cxOf e σ hj z).1 (j ''ᵁ W) ((j.appIso W).inv.hom g) := by
  have hle : W ≤ j ⁻¹ᵁ j ''ᵁ W := (j.preimage_image_eq W).ge
  change valR z.1 W g = valR (z.1 ≫ j) (j ''ᵁ W) _
  rw [← valR_appLE z.1 j hle hz, ← CommRingCat.comp_apply, Scheme.Hom.appIso_inv_appLE]
  exact (valR_res z.1 le_rfl hz g).symm

end Transfer

open GlobalTheory.Points Filter Topology

theorem finrank_eq_of_differentiableAt {E₁ E₂ : Type} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℂ E₂] (Φ : OpenPartialHomeomorph E₁ E₂) {x : E₁} (hx : x ∈ Φ.source)
    (h₁ : DifferentiableAt ℂ Φ x) (h₂ : DifferentiableAt ℂ Φ.symm (Φ x)) :
    Module.finrank ℂ E₁ = Module.finrank ℂ E₂ := by
  have hl : (fderiv ℂ Φ.symm (Φ x)).comp (fderiv ℂ Φ x) = ContinuousLinearMap.id ℂ E₁ :=
    ((h₂.hasFDerivAt.comp x h₁.hasFDerivAt).congr_of_eventuallyEq
      (EventuallyEq.symm (Φ.eventually_left_inverse hx : Φ.symm ∘ Φ =ᶠ[𝓝 x] id))).unique (hasFDerivAt_id x)
  have h₁' : HasFDerivAt Φ (fderiv ℂ Φ x) (Φ.symm (Φ x)) := by
    rw [Φ.left_inv hx]
    exact h₁.hasFDerivAt
  have hr : (fderiv ℂ Φ x).comp (fderiv ℂ Φ.symm (Φ x)) = ContinuousLinearMap.id ℂ E₂ :=
    ((h₁'.comp (Φ x) h₂.hasFDerivAt).congr_of_eventuallyEq
      (EventuallyEq.symm (Φ.eventually_right_inverse' hx : Φ ∘ Φ.symm =ᶠ[𝓝 (Φ x)] id))).unique (hasFDerivAt_id (Φ x))
  exact (ContinuousLinearEquiv.equivOfInverse (fderiv ℂ Φ x) (fderiv ℂ Φ.symm (Φ x))
    (fun v => DFunLike.congr_fun hl v) (fun v => DFunLike.congr_fun hr v)).toLinearEquiv.finrank_eq

section Transfer

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {σ : c.F →+* ℂ}

theorem differentiableAt_valAt'_symm {n g : ℕ} {ch₀ : OpenPartialHomeomorph (CxPts (genStr Z) σ) (Fin n → ℂ)}
    {ex : ExpMaps Z σ g} (h : IsExpChart ch₀ ex) (U : (gen Z).Opens) (f : Γ(gen Z, U)) {b : Fin n → ℂ}
    (hb : b ∈ ch₀.target) (hU : ⊤ ≤ (ch₀.symm b).1 ⁻¹ᵁ U) :
    DifferentiableAt ℂ (fun b => valAt' (ch₀.symm b).1 U f) b :=
  (h.2.2.1 U f).2.differentiableAt ((h.2.2.1 U f).1.mem_nhds ⟨hb, hU⟩)

end Transfer

theorem exists_holoChart_of_expChart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (X : Var F) (j : X.X ⟶ gen T.Z) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsOpenImmersion j → ∀ (y : GlobalTheory.CxPts X.str (σ.comp e.toRingHom)) (n g : ℕ) (ch₀ : OpenPartialHomeomorph (GlobalTheory.CxPts (genStr T.Z) σ) (Fin n → ℂ)) (ex : ExpMaps T.Z σ g), IsExpChart ch₀ ex → cxOf e σ hj y ∈ ch₀.source → ch₀ (cxOf e σ hj y) = 0 → ∀ r : ℝ, 0 < r → ∃ (hn : n = X.dim) (r' : ℝ) (ch : OpenPartialHomeomorph (GlobalTheory.CxPts X.str (σ.comp e.toRingHom)) (ReciprocityTheory.L2DbarEstimates.V X.dim)), 0 < r' ∧ r' < r ∧ r' < 1 ∧ IsHoloChart ch ∧ y ∈ ch.source ∧ ch y = 0 ∧ (∀ z ∈ ch.source, (ch z).ofLp ∈ GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.polydisc X.dim 1) ∧ ∀ z ∈ ch.source, cxOf e σ hj z ∈ ch₀.source ∧ ch₀ (cxOf e σ hj z) = fun k => (r' : ℂ) * (ch z).ofLp (Fin.cast hn k) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ X j hj hji y n g ch₀ ex hex hy0 hy00 r hr
  set κ := cxOf e σ hj with hκdef
  have hκ : IsOpenEmbedding κ := isOpenEmbedding_cxOf e σ hj
  haveI : Nonempty (GlobalTheory.CxPts X.str (σ.comp e.toRingHom)) := ⟨y⟩
  set χ := (hκ.toOpenPartialHomeomorph κ).trans ch₀ with hχdef
  have hχ : ∀ u ∈ χ.target, κ (χ.symm u) = ch₀.symm u := fun u hu => by
    have h2 : ch₀.symm u ∈ Set.range κ := by
      have := hu.2
      rwa [Set.mem_preimage, IsOpenEmbedding.toOpenPartialHomeomorph_target] at this
    rw [OpenPartialHomeomorph.coe_trans_symm, Function.comp_apply]
    exact hκ.toOpenPartialHomeomorph_right_inv κ h2
  have hyχ : y ∈ χ.source := ⟨trivial, hy0⟩
  have hχy : χ y = 0 := hy00
  obtain ⟨c₁, hc₁⟩ := GlobalTheory.AlgChart.exists_mem_source (p := X.str) (σ := σ.comp e.toRingHom) (D := X.dim) y
  have hn : n = X.dim := by
    set Φ := χ.symm.trans c₁.e with hΦ
    have h0 : (0 : Fin n → ℂ) ∈ Φ.source := by
      refine ⟨?_, ?_⟩
      · rw [← hχy]
        exact χ.map_source hyχ
      · show χ.symm 0 ∈ c₁.e.source
        rw [← hχy, χ.left_inv hyχ]
        exact hc₁
    have h0t : (0 : Fin n → ℂ) ∈ χ.target := h0.1
    have h1 : DifferentiableAt ℂ Φ 0 := by
      rw [differentiableAt_euclidean]
      intro a
      have hev : (fun u => Φ u a) =ᶠ[𝓝 0]
          fun u => valAt' (ch₀.symm u).1 (j ''ᵁ c₁.U) ((j.appIso c₁.U).inv.hom (c₁.x a)) := by
        filter_upwards [Φ.open_source.mem_nhds h0] with u hu
        have hs : χ.symm u ∈ c₁.e.source := hu.2
        show c₁.e (χ.symm u) a = _
        rw [c₁.apply_eq _ hs a, ev_eq_valAt'_cxOf e σ hj _ _ (c₁.source_subset hs),
          show cxOf e σ hj (χ.symm u) = ch₀.symm u from hχ u hu.1]
      refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
      refine differentiableAt_valAt'_symm hex _ _ h0t.1 ?_
      rw [← hχ 0 h0t]
      exact le_preimage_cxOf e σ hj _ (c₁.source_subset h0.2)
    have h2 : DifferentiableAt ℂ Φ.symm (Φ 0) := by
      have hB : IsOpen Φ.target := Φ.open_target
      have hΦ0 : Φ 0 ∈ Φ.target := Φ.map_source h0
      have hsub : Φ.target ⊆ c₁.e.target := fun w hw => hw.1
      have hmaps : Set.MapsTo (fun w => κ (c₁.e.symm w)) Φ.target ch₀.source := fun w hw => hw.2.2
      have hhol : IsHolTo Φ.target (fun w => (κ (c₁.e.symm w)).1) := by
        intro U f
        have hset : {b ∈ Φ.target | ⊤ ≤ (κ (c₁.e.symm b)).1 ⁻¹ᵁ U} =
            Φ.target ∩ c₁.e.symm ⁻¹' ptsIn X.str (σ.comp e.toRingHom) (j ⁻¹ᵁ U) := rfl
        refine ⟨?_, ?_⟩
        · rw [hset]
          exact (c₁.e.continuousOn_symm.mono hsub).isOpen_inter_preimage hB (isOpen_ptsIn _)
        · rw [hset]
          refine ((c₁.holo (j ⁻¹ᵁ U) ((j.app U).hom f)).mono fun w (hw : w ∈ Φ.target ∩ c₁.e.symm ⁻¹' ptsIn X.str (σ.comp e.toRingHom) (j ⁻¹ᵁ U)) => ⟨hsub hw.1, hw.2⟩).congr
            fun w _ => ?_
          exact valR_comp (c₁.e.symm w).1 j U f
      rw [differentiableAt_pi]
      intro k
      have hd := (hex.2.1 k (ReciprocityTheory.L2DbarEstimates.V X.dim) Φ.target (fun w => κ (c₁.e.symm w)) hB hhol hmaps).differentiableAt
        (hB.mem_nhds hΦ0)
      exact hd
    have := finrank_eq_of_differentiableAt Φ h0 h1 h2
    simpa [finrank_euclideanSpace_fin] using this
  subst hn
  have hr1 : 0 < min r 1 := lt_min hr one_pos
  set r' : ℝ := min r 1 / 2 with hr'
  have hr'0 : 0 < r' := half_pos hr1
  have hr'r : r' < min r 1 := half_lt_self hr1
  have hr'c : (r' : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr'0.ne'
  let L : (Fin X.dim → ℂ) ≃L[ℂ] ReciprocityTheory.L2DbarEstimates.V X.dim :=
    (ContinuousLinearEquiv.smulLeft (Units.mk0 ((r' : ℂ)⁻¹) (inv_ne_zero hr'c))).trans
      (EuclideanSpace.equiv (Fin X.dim) ℂ).symm
  have hL : ∀ u k, (L u).ofLp k = (r' : ℂ)⁻¹ * u k := by
    intro u k
    simp [L]
  let ch := (χ.trans (OpenPartialHomeomorph.ofSet (Metric.ball (0 : Fin X.dim → ℂ) r') Metric.isOpen_ball)).trans
    L.toHomeomorph.toOpenPartialHomeomorph
  have hchs : ∀ v, ch.symm v = χ.symm (L.symm v) := fun v => rfl
  have hch : ∀ z, ch z = L (χ z) := fun z => rfl
  have hsrc : ∀ z ∈ ch.source, z ∈ χ.source ∧ χ z ∈ Metric.ball (0 : Fin X.dim → ℂ) r' := fun z hz => hz.1
  have htgt : ∀ v ∈ ch.target, L.symm v ∈ χ.target := fun v hv => hv.2.2
  refine ⟨rfl, r', ch, hr'0, hr'r.trans_le (min_le_left _ _), hr'r.trans_le (min_le_right _ _), ?_,
    ⟨⟨hyχ, ?_⟩, trivial⟩, ?_, ?_, ?_⟩
  · intro W f v hv
    have hopen : IsOpen (ch.target ∩ ch.symm ⁻¹' ptsIn X.str (σ.comp e.toRingHom) W) :=
      ch.continuousOn_symm.isOpen_inter_preimage ch.open_target (isOpen_ptsIn W)
    refine DifferentiableAt.differentiableWithinAt ?_
    have hev : (ev X.str (σ.comp e.toRingHom) W f ∘ ch.symm) =ᶠ[𝓝 v]
        fun w => valAt' (ch₀.symm (L.symm w)).1 (j ''ᵁ W) ((j.appIso W).inv.hom f) := by
      filter_upwards [hopen.mem_nhds hv] with w hw
      rw [Function.comp_apply, ev_eq_valAt'_cxOf e σ hj W f hw.2, hchs,
        show cxOf e σ hj (χ.symm (L.symm w)) = ch₀.symm (L.symm w) from hχ _ (htgt w hw.1)]
    refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
    have hb := htgt v hv.1
    refine (differentiableAt_valAt'_symm hex (j ''ᵁ W) _ hb.1 ?_).comp v L.symm.differentiableAt
    rw [← hχ _ hb]
    exact le_preimage_cxOf e σ hj W hv.2
  · show χ y ∈ Metric.ball 0 r'
    rw [hχy]
    exact Metric.mem_ball_self hr'0
  · rw [hch, hχy, map_zero]
  · intro z hz
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.polydisc, Set.mem_setOf_eq]
    intro k
    rw [hch, hL, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hr'0.le]
    have h1 := (hsrc z hz).2
    rw [mem_ball_zero_iff] at h1
    have h2 : ‖χ z k‖ < r' := (norm_le_pi_norm (χ z) k).trans_lt h1
    calc r'⁻¹ * ‖χ z k‖ < r'⁻¹ * r' := mul_lt_mul_of_pos_left h2 (inv_pos.2 hr'0)
      _ = 1 := inv_mul_cancel₀ hr'0.ne'
  · intro z hz
    refine ⟨hz.1.1.2, ?_⟩
    funext k
    show χ z k = _
    rw [hch, hL, Fin.cast_eq_self, ← mul_assoc, mul_inv_cancel₀ hr'c, one_mul]

end GlobalTheory.LieBase
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTamePolyhedralFan
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models

noncomputable section

namespace GlobalTheory.PolFan.TameZ

variable {g n m : ℕ}


variable {φ : InvFun ℤ}

theorem toReal_mem_psdCone_int {X : Type} [AddCommGroup X] [Module.Finite ℤ X] {β : LinearMap.BilinForm ℤ X}
    (hβ : β ∈ balForms (id : ℤ → ℤ) X) (hp : ∀ y, 0 ≤ β y y) : toReal β ∈ psdCone (bar := (id : ℤ → ℤ)) (X := X) := by
  have := ConeSub.sum_smul_toReal_mem_psdCone ℤ id X 1 ![β] ![1] (by simp [hβ]) (by simp [hp]) (by simp)
  simpa using this

end GlobalTheory.PolFan.TameZ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsVarietyConnectedComponentGenericFibre
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

namespace GlobalTheory.CompOfVar

theorem exists_var_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F), SmoothOfRelativeDimension Dw.dim (genStr Z) → ∀ (Y : Var F) (π : Y.X ⟶ gen Z), π ≫ genStr Z ≫ spMap e.toRingHom = Y.str → ∃ (X : Var F) (j : X.X ⟶ gen Z), IsOpenImmersion j ∧ j ≫ genStr Z ≫ spMap e.toRingHom = X.str ∧ Set.range π ⊆ Set.range j := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e hsm Y π hπ
  have hS : Smooth (genStr Z) := SmoothOfRelativeDimension.smooth Dw.dim _
  have := isProper_genStr Z
  have : IsLocallyNoetherian (gen Z) := LocallyOfFiniteType.isLocallyNoetherian (genStr Z)
  have : CompactSpace (gen Z) := QuasiCompact.compactSpace_of_compactSpace (genStr Z)
  have : IsNoetherian (gen Z) := {}
  have hcc := fun z : gen Z => PtComp.connectedComponent_mem
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
    (fun W hW W' hW' => PtComp.disjoint_of_smooth (genStr Z) hS W W' hW hW') z
  let z : gen Z := π (genericPoint Y.X)
  let V : (gen Z).Opens := ⟨connectedComponent z, (hcc z).2⟩
  have hred : IsReduced (gen Z) := by
    have := GlobalTheory.isNormalScheme_of_smooth (genStr Z)
    exact GlobalTheory.IsNormalScheme.isReduced
  have : CharZero F := e.toRingHom.charZero
  have : IsIso (spMap e.toRingHom) :=
    inferInstanceAs (IsIso (Spec.map e.toCommRingCatIso.hom))
  have hproj : IsProjOver (genStr Z ≫ spMap e.toRingHom) := GlobalTheory.GenFibreComp.isProjOver_comp_equiv e _
    ((GlobalTheory.ProjSpace.points_and_stability O 0).2.2.1 c.F β Z.X Z.s Z.proj)
  have : IrreducibleSpace V.toScheme := Subtype.irreducibleSpace (hcc z).1.1
  have : IsIntegral V.toScheme := isIntegral_of_irreducibleSpace_of_isReduced _
  have hcl : IsClosedImmersion V.ι := IsClosedImmersion.of_isPreimmersion _ (by
    rw [Scheme.Opens.range_ι]; exact isClosed_connectedComponent)
  have hp : IsProjOver (V.ι ≫ genStr Z ≫ spMap e.toRingHom) :=
    (GlobalTheory.ProjSpace.points_and_stability F 0).2.2.2.1 _ _ _ _ hcl hproj
  have hsd : SmoothOfRelativeDimension Dw.dim (V.ι ≫ genStr Z ≫ spMap e.toRingHom) := by
    have h : SmoothOfRelativeDimension (0 + (Dw.dim + 0)) (V.ι ≫ genStr Z ≫ spMap e.toRingHom) := inferInstance
    simpa using h
  have hr : Set.range π ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    exact (isPreconnected_range π.continuous).subset_connectedComponent ⟨_, rfl⟩
  let g : Y.X ⟶ V.toScheme := IsOpenImmersion.lift V.ι π hr
  have hg : g ≫ V.ι = π := IsOpenImmersion.lift_fac _ _ _
  have : Smooth (V.ι ≫ genStr Z ≫ spMap e.toRingHom) := SmoothOfRelativeDimension.smooth Dw.dim _
  have : GlobalTheory.IsNormalScheme V.toScheme := GlobalTheory.ModifSections.isNormalScheme_of_smooth (V.ι ≫ genStr Z ≫ spMap e.toRingHom)
  have : GeometricallyConnected (V.ι ≫ genStr Z ≫ spMap e.toRingHom) := by
    refine GlobalTheory.GeomConnFn.geometricallyConnected_of_locallyOfFiniteType _ ?_
    exact _root_.GlobalTheory.ConstDescent.descent F V.toScheme Y.X _ Y.str g (by rw [reassoc_of% hg, hπ])
      (GlobalTheory.T.geometricallyIntegral_algebraicConstants_mem_range F Y.X Y.str)
  obtain ⟨X, ε, -, hs⟩ := GlobalTheory.ProjVar.Var.exists_iso _ Dw.dim hp
  refine ⟨X, ε.inv ≫ V.ι, inferInstance, ?_, ?_⟩
  · rw [Category.assoc, ← hs, Iso.inv_hom_id_assoc]
  · rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, ε.inv.surjective.range_eq, Set.image_univ]
    exact hr

end GlobalTheory.CompOfVar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointPoly
section
noncomputable section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LieBase

variable {E : Type} [Field E] [NumberField E] [IsCMField E]


open Classical in
def pointPoly (H : Host E) (Dw : Datum H) : MvPolynomial ((E →+* ℂ) × ℕ) ℝ :=
  ∏ τ : GlobalTheory.AllWt.Psi H, (C ((-1 : ℝ) ^ Dw.mult τ.1) * X (τ.1, Dw.mult τ.1)) ^ (Dw.p + Dw.q - Dw.mult τ.1)

end GlobalTheory.LieBase
end
end

