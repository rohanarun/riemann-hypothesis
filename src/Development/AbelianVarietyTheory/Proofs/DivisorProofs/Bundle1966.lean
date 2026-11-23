module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1902
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0547
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1380
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0544
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1936

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundlePointsEqOfSameStepsLocalRing
section
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)

namespace GlobalTheory.FlagMod.FieldFlag

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {p : Proj (RingHom.id c.F)} {A : Atlas Y p}
  {Z : Scheme.{0}} {π : Z ⟶ Y.X} {g : ∀ en : En Dw.mult, Z ⟶ PSpace c.F (plN A.N en.1)}
  {κ : ∀ b, Pm Dw.mult → (Sp (CR Dw.mult (A.V b)) ⟶ Z)} [∀ b w, IsOpenImmersion (κ b w)]
  {S : Type} [CommRing S]

theorem spMap_comp_spMap_cell {R R' U : Type} [CommRing R] [CommRing R'] [CommRing U] (f : R →+* R')
    (f' : R' →+* U) : spMap f' ≫ spMap f = spMap (f'.comp f) :=
  (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom f')).symm

theorem base_cellPt (hZ : Cells A π g κ) (k : A.B × Pm Dw.mult) (z : Sp S ⟶ Z)
    (hz : ⊤ ≤ z ⁻¹ᵁ (κ k.1 k.2).opensRange) :
    z ≫ π = spMap (((ev z _ hz).comp (cellθ κ k).toRingHom).comp MvPolynomial.C) ≫ tau (A.aff k.1) := by
  conv_lhs => rw [← eq_spMap_ev k z hz]
  rw [Category.assoc, hZ.plk.base, cbase, ← Category.assoc, spMap_comp_spMap_cell]
  rfl

theorem le_cellPt (hZ : Cells A π g κ) (k : A.B × Pm Dw.mult) (z : Sp S ⟶ Z)
    (hz : ⊤ ≤ z ⁻¹ᵁ (κ k.1 k.2).opensRange) {x : Sp S ⟶ Y.X} (hx : z ≫ π = x) : ⊤ ≤ x ⁻¹ᵁ (A.k k.1).V := by
  rw [← hx, base_cellPt hZ k z hz]
  exact le_preimage_comp _ (tau_le (A.aff k.1) le_rfl)

theorem g_cellPt (hZ : Cells A π g κ) (ht : FlagCellFrameChangeTriangular hZ) (k : A.B × Pm Dw.mult) (z : Sp S ⟶ Z)
    (hz : ⊤ ≤ z ⁻¹ᵁ (κ k.1 k.2).opensRange) {x : Sp S ⟶ Y.X} (hx : z ≫ π = x) (hV : ⊤ ≤ x ⁻¹ᵁ (A.k k.1).V)
    (en : En Dw.mult) :
    ∃ hu, z ≫ g en = pt (str x) (plk (fun (t : Let Dw.mult) r =>
      ((A.A k.1).map (ev x _ hV) * (show Matrix (Fin (A.k k.1).M.n) (Fin (Dw.mult t.1)) S from
        (cellFrames hZ ht).uAt k z hz t.1)) r t.2) en.2.1) hu := by
  have hb := base_cellPt hZ k z hz
  set φ := (ev z _ hz).comp (cellθ κ k).toRingHom with hφ
  have hev : ev x _ hV = φ.comp MvPolynomial.C := by
    subst hx
    rw [ev_congr hb _ hV (hb ▸ hV)]
    exact ev_spMap_tau _ _ _
  have hstr : str x = (φ.comp MvPolynomial.C).comp (A.alpha k.1) := by
    refine LowRank.str_eq ?_
    rw [← hx, hb, Category.assoc, ← spMap_comp_spMap_cell (A.alpha k.1) (φ.comp MvPolynomial.C)]
    congr 1
    exact (spMap_ev_top _).symm
  obtain ⟨hu, e⟩ := hZ.plk.plk k.1 k.2 en
  have key : ∀ (f f' : c.F →+* S) (v v' : Fin (plN A.N en.1 + 1) → S) hv, f = f' → v = v' →
      ∃ hv', pt f v hv = pt f' v' hv' := by
    rintro f _ v _ hv rfl rfl
    exact ⟨hv, rfl⟩
  conv => enter [1, hu']; lhs; rw [← eq_spMap_ev k z hz]
  rw [Category.assoc, e]
  have hspan : Ideal.span (Set.range (φ ∘ plk (uvec (A.cv k.1) k.2) en.2.1)) = ⊤ := by
    rw [Set.range_comp, ← Ideal.map_span, hu, Ideal.map_top]
  letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (plN A.N en.1 + 1)) c.F) := MvPolynomial.gradedAlgebra
  have hmap : spMap φ ≫ pt (MvPolynomial.C.comp ((A.alpha k.1).comp (RingHom.id c.F)))
      (plk (uvec (A.cv k.1) k.2) en.2.1) hu =
      pt (φ.comp (MvPolynomial.C.comp ((A.alpha k.1).comp (RingHom.id c.F))))
        (φ ∘ plk (uvec (A.cv k.1) k.2) en.2.1)
        hspan := by
    refine (ProjPoint.SpecMap_ofHom _ _ _ φ).trans ?_
    unfold pt
    congr 1
    exact MvPolynomial.ringHom_ext (fun r => by simp) (fun i => by simp)
  rw [hmap]
  refine key _ _ _ _ _ (by rw [hstr]; rfl) ?_
  rw [map_plk]
  congr 1
  funext t r
  rw [Function.comp_apply, uvec_cv]
  show φ _ = _
  rw [← Matrix.map_apply (f := φ), Matrix.map_mul, Matrix.map_map, hev]
  rfl

end GlobalTheory.FlagMod.FieldFlag

namespace GlobalTheory.FlagMod.FieldFlag

open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem cell_sep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) (A : Atlas Y p) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (g : ∀ en : En Dw.mult, Z ⟶ PSpace c.F (plN A.N en.1)) (κ : ∀ b, Pm Dw.mult → (Sp (CR Dw.mult (A.V b)) ⟶ Z)) [∀ b w, IsOpenImmersion (κ b w)] (hZ : Cells A π g κ) (ht : FlagCellFrameChangeTriangular hZ) (S : Type) [CommRing S] [IsLocalRing S] (z z' : Sp S ⟶ Z) (x : Sp S ⟶ Y.X) (hx : z ≫ π = x) (hx' : z' ≫ π = x), (∀ σ i, (cellFrames hZ ht).step z hx σ i = (cellFrames hZ ht).step z' hx' σ i) → z = z' := by
  intro E _ _ _ H Dw l Xo c Y p A Z π g κ _ hZ ht S _ _ z z' x hx hx' hst
  obtain ⟨k, hz⟩ := exists_chart_of_isLocalRing (cellFrames hZ ht).cover z
  obtain ⟨k', hz'⟩ := exists_chart_of_isLocalRing (cellFrames hZ ht).cover z'
  have hV := le_cellPt hZ k z hz hx
  have hV' := le_cellPt hZ k' z' hz' hx'
  have hM : ⊤ ≤ x ⁻¹ᵁ ((A.k k.1).M.U ⊓ (A.k k'.1).M.U) :=
    le_preimage_inf ((cellFrames hZ ht).inM hz hx) ((cellFrames hZ ht).inM hz' hx')

  have ex : ∀ σ, ∃ b : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S, b.BlockTriangular id ∧ (∀ i, IsUnit (b i i)) ∧
      ∀ i, (cellFrames hZ ht).vecAt k' z' hz' hx' σ i = ∑ j, b j i • (cellFrames hZ ht).vecAt k z hz hx σ j :=
    fun σ => exists_tri_of_eq ((cellFrames hZ ht).linearIndependent_vecAt k z hz hx σ) fun i => by
      rw [← (cellFrames hZ ht).step_eq k z hz hx, ← (cellFrames hZ ht).step_eq k' z' hz' hx', hst]
  choose B hB hBu hBe using ex
  obtain ⟨a, ha⟩ := A.tw S x k'.1 k.1 hV' hV hM

  have hU : ∀ σ, (chg (A.k k.1).M.toMChart (A.k k'.1).M.toMChart).map (ev x _ hM) *
      (show Matrix (Fin (A.k k'.1).M.n) (Fin (Dw.mult σ)) S from (cellFrames hZ ht).uAt k' z' hz' σ) =
      (show Matrix (Fin (A.k k.1).M.n) (Fin (Dw.mult σ)) S from (cellFrames hZ ht).uAt k z hz σ) * B σ := by
    intro σ
    ext r i
    have e := hBe σ i
    rw [(cellFrames hZ ht).sum_vecAt k z hz hx σ (fun j => B σ j i)] at e
    have e2 := vec_chg (A.k k.1).M.toMChart (A.k k'.1).M.toMChart x ((cellFrames hZ ht).inM hz hx)
      ((cellFrames hZ ht).inM hz' hx') hM (fun j => (cellFrames hZ ht).uAt k' z' hz' σ j i)
    have e3 := congrFun ((vec _ _ _).injective (e2.trans e)) r
    rw [Matrix.mul_apply, Matrix.mul_apply]
    simpa [Matrix.mulVec, dotProduct] using e3

  have hc : ∀ (t : Let Dw.mult), (fun r => ((A.A k'.1).map (ev x _ hV') *
      (show Matrix (Fin (A.k k'.1).M.n) (Fin (Dw.mult t.1)) S from (cellFrames hZ ht).uAt k' z' hz' t.1)) r t.2) =
      ∑ j, (a * B t.1 j t.2 : S) • fun r => ((A.A k.1).map (ev x _ hV) *
      (show Matrix (Fin (A.k k.1).M.n) (Fin (Dw.mult t.1)) S from (cellFrames hZ ht).uAt k z hz t.1)) r j := by
    intro t
    funext r
    rw [ha, Matrix.smul_mul, Matrix.mul_assoc, hU t.1, ← Matrix.mul_assoc]
    simp only [Matrix.smul_apply, smul_eq_mul, Finset.sum_apply, Pi.smul_apply]
    rw [Matrix.mul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have htri : Tri (fun (t : Let Dw.mult) r => ((A.A k.1).map (ev x _ hV) *
      (show Matrix (Fin (A.k k.1).M.n) (Fin (Dw.mult t.1)) S from (cellFrames hZ ht).uAt k z hz t.1)) r t.2)
      (fun (t : Let Dw.mult) r => ((A.A k'.1).map (ev x _ hV') *
      (show Matrix (Fin (A.k k'.1).M.n) (Fin (Dw.mult t.1)) S from (cellFrames hZ ht).uAt k' z' hz' t.1)) r t.2)
      (fun t => a * B t.1 t.2 t.2) := by
    rintro ⟨σ, i⟩
    have h1 := hc ⟨σ, i⟩
    dsimp only at h1 ⊢
    rw [h1, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), add_sub_cancel_left]
    refine Submodule.sum_mem _ fun j hj => ?_
    rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hj) with h | h
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, h, rfl⟩)
    · rw [hB σ (show id i < id j from h), mul_zero, zero_smul]
      exact Submodule.zero_mem _
  refine hZ.ext _ z z' (hx.trans hx'.symm) fun en => ?_
  obtain ⟨hu, e⟩ := g_cellPt hZ ht k z hz hx hV en
  obtain ⟨hu', e'⟩ := g_cellPt hZ ht k' z' hz' hx' hV' en
  rw [e, e']
  have hd : IsUnit (∏ l, a * B (en.2.1 l).1 (en.2.1 l).2 (en.2.1 l).2) :=
    IsUnit.prod_univ_iff.2 fun l => a.isUnit.mul (hBu _ _)
  exact (pt_eq_pt_iff _ hu hu').2 ⟨hd.unit, by rw [plk_tri _ _ S A.N _ _ _ en.1 en.2.1 htri en.2.2]; rfl⟩

end GlobalTheory.FlagMod.FieldFlag
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCellPointImageAndFrame
section
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem actR)
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.FlagMod.FieldFlag

theorem spMap_comp_cellpt {R₁ R₂ R₃ : Type} [CommRing R₁] [CommRing R₂] [CommRing R₃] (f : R₁ →+* R₂)
    (g : R₂ →+* R₃) : spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem cellpt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) (A : Atlas Y p) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (g : ∀ en : En Dw.mult, Z ⟶ PSpace c.F (plN A.N en.1)) (κ : ∀ b, Pm Dw.mult → (Sp (CR Dw.mult (A.V b)) ⟶ Z)) [∀ b w, IsOpenImmersion (κ b w)] (hZ : Cells A π g κ) (ht : FlagCellFrameChangeTriangular hZ) (b : A.B) (w : Pm Dw.mult) (S : Type) [CommRing S] (ψ₀ : Γ(Y.X, (A.V b).1) →+* S) (xc : CellVar Dw.mult → S) (z : Sp S ⟶ Z), z = spMap (MvPolynomial.eval₂Hom ψ₀ xc) ≫ κ b w → z ≫ π = spMap ψ₀ ≫ (A.V b).2.fromSpec ∧ ∃ hz : ⊤ ≤ z ⁻¹ᵁ (cellFrames hZ ht).U ((b, w) : A.B × Pm Dw.mult), ∀ σ, (cellFrames hZ ht).uAt ((b, w) : A.B × Pm Dw.mult) z hz σ = (((A.k b).u σ).map ψ₀).submatrix id (w σ) * Matrix.of (cell xc σ) := by
  intro E _ _ _ H Dw l Xo c Y p A Z π g κ _ hZ ht b w S _ ψ₀ xc z hzd
  refine ⟨?_, ?_⟩
  · rw [hzd, Category.assoc, hZ.plk.base b w, cbase, ← Category.assoc, spMap_comp_cellpt,
      MvPolynomial.eval₂Hom_comp_C]
  · have hz : ⊤ ≤ z ⁻¹ᵁ (cellFrames hZ ht).U ((b, w) : A.B × Pm Dw.mult) := by
      intro x _
      show z x ∈ Set.range (κ b w)
      rw [hzd, Scheme.Hom.comp_apply]
      exact ⟨_, rfl⟩
    refine ⟨hz, fun σ => ?_⟩
    have key : (ev z _ hz).comp (cellθ κ ((b, w) : A.B × Pm Dw.mult)).toRingHom = MvPolynomial.eval₂Hom ψ₀ xc := by
      have h1 := eq_spMap_ev (κ := κ) ((b, w) : A.B × Pm Dw.mult) z hz
      have h2 : spMap ((ev z _ hz).comp (cellθ κ ((b, w) : A.B × Pm Dw.mult)).toRingHom) =
          spMap (MvPolynomial.eval₂Hom ψ₀ xc) := by
        rw [← cancel_mono (κ b w)]
        exact h1.trans hzd
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective h2)
    show ((uC A b w σ).map (cellθ κ ((b, w) : A.B × Pm Dw.mult))).map (ev z _ hz) = _
    change (uC A b w σ).map ((ev z _ hz).comp (cellθ κ ((b, w) : A.B × Pm Dw.mult)).toRingHom) = _
    rw [key, uC, Matrix.map_mul, Matrix.submatrix_map, Matrix.map_map]
    congr 1
    · congr 1
      ext i j
      simp [cC]
    · ext i j
      simp only [cellMat, Matrix.map_apply, Matrix.of_apply, cell]
      split_ifs <;> simp

end GlobalTheory.FlagMod.FieldFlag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCellsFramesTriangular
section
noncomputable section

namespace GlobalTheory.FlagMod.FieldFlag

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace
open GlobalTheory.FlagMod.LowRank (ECh Proj str)

theorem tri_of_cols {L : Type} [CommRing L] {n m : ℕ} (U : Matrix (Fin n) (Fin m) L) (Wm : Matrix (Fin m) (Fin n) L)
    (hWU : Wm * U = 1) (V : Matrix (Fin n) (Fin m) L)
    (h : ∀ j, ∃ a : Fin m → L, (∀ i, j < i → a i = 0) ∧ (fun r => V r j) = U.mulVec a) :
    V = U * (Wm * V) ∧ ∀ i j, j < i → (Wm * V) i j = 0 := by
  choose a ha hV using h
  have hc : ∀ j, (fun i => (Wm * V) i j) = a j := fun j => by
    have e : (fun i => (Wm * V) i j) = Wm.mulVec (fun r => V r j) := by
      funext i; simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rw [e, hV j, Matrix.mulVec_mulVec, hWU, Matrix.one_mulVec]
  refine ⟨?_, fun i j hij => ?_⟩
  · ext r j
    have e1 := congrFun (hV j) r
    have e2 : (U * (Wm * V)) r j = U.mulVec (fun i => (Wm * V) i j) r := by
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rw [e2, hc j]
    exact e1
  · exact (congrFun (hc j) i).trans (ha j i hij)

theorem spMap_comp_spMap {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {p : Proj (RingHom.id c.F)} {A : Atlas Y p}
  {Z : Scheme.{0}} {π : Z ⟶ Y.X} {g : ∀ en : En Dw.mult, Z ⟶ PSpace c.F (plN A.N en.1)}
  {κ : ∀ b, Pm Dw.mult → (Sp (CR Dw.mult (A.V b)) ⟶ Z)} [∀ b w, IsOpenImmersion (κ b w)]

theorem comp_base (hZ : Cells A π g κ) (k : A.B × Pm Dw.mult) {L : Type} [CommRing L] (z : Sp L ⟶ Z)
    (hz : ⊤ ≤ z ⁻¹ᵁ (κ k.1 k.2).opensRange) :
    z ≫ π = spMap (((ev z _ hz).comp (cellθ κ k).toRingHom).comp (cC A k.1)) ≫ tau (A.V k.1).2 := by
  conv_lhs => rw [← eq_spMap_ev k z hz]
  rw [Category.assoc, hZ.plk.base, cbase, ← Category.assoc, spMap_comp_spMap]
  rfl

theorem le_comp_base (hZ : Cells A π g κ) (k : A.B × Pm Dw.mult) {L : Type} [CommRing L] (z : Sp L ⟶ Z)
    (hz : ⊤ ≤ z ⁻¹ᵁ (κ k.1 k.2).opensRange) : ⊤ ≤ (z ≫ π) ⁻¹ᵁ (A.V k.1).1 := by
  rw [comp_base hZ k z hz]
  exact le_preimage_comp _ (tau_le _ le_rfl)

theorem ev_comp_base (hZ : Cells A π g κ) (k : A.B × Pm Dw.mult) {L : Type} [CommRing L] (z : Sp L ⟶ Z)
    (hz : ⊤ ≤ z ⁻¹ᵁ (κ k.1 k.2).opensRange) (h : ⊤ ≤ (z ≫ π) ⁻¹ᵁ (A.V k.1).1) :
    ev (z ≫ π) _ h = ((ev z _ hz).comp (cellθ κ k).toRingHom).comp (cC A k.1) := by
  rw [ev_congr (comp_base hZ k z hz) _ h (by rw [← comp_base hZ k z hz]; exact h)]
  exact ev_spMap_tau _ _ _

theorem ne_zero_of_span_eq_top {L ι : Type} [Field L] [Fintype ι] {v : ι → L} (h : Ideal.span (Set.range v) = ⊤) :
    v ≠ 0 := by
  rintro rfl
  have h2 : (1 : L) ∈ Ideal.span (Set.range (0 : ι → L)) := h ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.1 h2
  simp at hc

theorem col_tri (hZ : Cells A π g κ) (k k' : A.B × Pm Dw.mult) (σ : E →+* ℂ) {L : Type} [Field L] (z : Sp L ⟶ Z)
    (hz : ⊤ ≤ z ⁻¹ᵁ (κ k.1 k.2).opensRange) (hz' : ⊤ ≤ z ⁻¹ᵁ (κ k'.1 k'.2).opensRange)
    (hM : ⊤ ≤ (z ≫ π) ⁻¹ᵁ ((A.k k.1).M.U ⊓ (A.k k'.1).M.U)) (j : Fin (Dw.mult σ)) :
    ∃ a : Fin (Dw.mult σ) → L, (∀ i, j < i → a i = 0) ∧
      ((chg (A.k k.1).M.toMChart (A.k k'.1).M.toMChart).map (ev (z ≫ π) _ hM)).mulVec
        (fun s => ((ev z _ hz').comp (cellθ κ k').toRingHom) (uC A k'.1 k'.2 σ s j)) =
      ((uC A k.1 k.2 σ).map ((ev z _ hz).comp (cellθ κ k).toRingHom)).mulVec a := by
  classical
  have span_range_comp_eq_top : ∀ {A B : Type} [CommRing A] [CommRing B] {n : ℕ}
      (v : Fin (n + 1) → A), Ideal.span (Set.range v) = ⊤ → (ψ : A →+* B) →
      Ideal.span (Set.range (ψ ∘ v)) = ⊤ := by
    intro A B _ _ n v hv ψ
    rw [Set.range_comp, ← Ideal.map_span, hv, Ideal.map_top]
  have spMap_pt : ∀ {O A B : Type} [CommRing O] [CommRing A] [CommRing B] {n : ℕ}
      (c : O →+* A) (v : Fin (n + 1) → A) (hv : Ideal.span (Set.range v) = ⊤) (ψ : A →+* B),
      spMap ψ ≫ pt c v hv = pt (ψ.comp c) (ψ ∘ v) (span_range_comp_eq_top v hv ψ) := by
    intro O A B _ _ _ n c v hv ψ
    letI := MvPolynomial.gradedAlgebra (σ := Fin (n + 1)) (R := O)
    refine (ProjPoint.SpecMap_ofHom _ _ _ ψ).trans ?_
    unfold pt
    congr 1
    exact MvPolynomial.ringHom_ext (fun r => by simp) (fun i => by simp)
  have pt_str : ∀ {O A : Type} [CommRing O] [CommRing A] {N : ℕ}
      (c : O →+* A) (v : Fin (N + 1) → A) (hv : Ideal.span (Set.range v) = ⊤),
      pt c v hv ≫ PSpace.str O N = spMap c := by
    intro O A _ _ N c v hv
    rw [pt, PSpace.str, ProjPoint.ofHom_toSpecZero_assoc, ← Spec.map_comp]
    congr 1
    ext1
    exact RingHom.ext fun r => MvPolynomial.eval₂Hom_C c v r
  have hx := le_comp_base hZ k z hz
  have hx' := le_comp_base hZ k' z hz'
  have ex := ev_comp_base hZ k z hz hx
  have ex' := ev_comp_base hZ k' z hz' hx'
  have ez := eq_spMap_ev k z hz
  have ez' := eq_spMap_ev k' z hz'
  obtain ⟨a0, ha0⟩ := A.tw L (z ≫ π) k'.1 k.1 hx' hx hM
  rw [ex, ex'] at ha0
  generalize (chg (A.k k.1).M.toMChart (A.k k'.1).M.toMChart).map (ev (z ≫ π) _ hM) = Chx at ha0 ⊢
  generalize (ev z _ hz).comp (cellθ κ k).toRingHom = ψ at ez ha0 ⊢
  generalize (ev z _ hz').comp (cellθ κ k').toRingHom = ψ' at ez' ha0 ⊢
  have hj : j.1 + 1 ≤ Dw.mult σ := j.2
  obtain ⟨hu, hp⟩ := hZ.plk.plk k.1 k.2 (stdEn σ (j.1 + 1) hj)
  obtain ⟨hu', hp'⟩ := hZ.plk.plk k'.1 k'.2 (stdEn σ (j.1 + 1) hj)
  have e1 : z ≫ g (stdEn σ (j.1 + 1) hj) = pt (ψ.comp ((MvPolynomial.C).comp ((A.alpha k.1).comp (RingHom.id c.F))))
      (ψ ∘ plk (uvec (A.cv k.1) k.2) (std σ (j.1 + 1) hj)) (span_range_comp_eq_top _ hu ψ) := by
    rw [← ez, Category.assoc, hp, spMap_pt]
  have e2 : z ≫ g (stdEn σ (j.1 + 1) hj) = pt (ψ'.comp ((MvPolynomial.C).comp ((A.alpha k'.1).comp (RingHom.id c.F))))
      (ψ' ∘ plk (uvec (A.cv k'.1) k'.2) (std σ (j.1 + 1) hj)) (span_range_comp_eq_top _ hu' ψ') := by
    rw [← ez', Category.assoc, hp', spMap_pt]
  have ec : ψ.comp ((MvPolynomial.C).comp ((A.alpha k.1).comp (RingHom.id c.F))) =
      ψ'.comp ((MvPolynomial.C).comp ((A.alpha k'.1).comp (RingHom.id c.F))) := by
    have := congrArg (· ≫ PSpace.str c.F _) (e1.symm.trans e2)
    simp only [pt_str] at this
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective this)
  obtain ⟨u, hu2⟩ := (pt_eq_pt_iff _ (span_range_comp_eq_top _ hu ψ) (span_range_comp_eq_top _ hu' ψ')).1
    (e1.symm.trans (e2.trans (congrArg (fun c => pt c _ _) ec.symm)))
  let cv : Fin (j.1 + 1) → Fin (A.N + 1) → L := fun l => ψ ∘ uvec (A.cv k.1) k.2 (std σ (j.1 + 1) hj l)
  let cv' : Fin (j.1 + 1) → Fin (A.N + 1) → L := fun l => ψ' ∘ uvec (A.cv k'.1) k'.2 (std σ (j.1 + 1) hj l)
  have hpl : plk cv' id = (u : L) • plk cv id := by
    have := hu2
    rw [map_plk, map_plk, Units.smul_def] at this
    exact this
  have h0 : plk cv' id ≠ 0 := fun h =>
    ne_zero_of_span_eq_top (span_range_comp_eq_top _ hu' ψ') (by rw [map_plk]; exact h)
  have hmem := mem_span_of_plk_eq_smul L A.N (j.1 + 1) cv cv' u h0 hpl (Fin.last j.1)
  obtain ⟨f, hf⟩ := (Submodule.mem_span_range_iff_exists_fun L).1 hmem
  have hcol : ∀ (b : A.B) (w : Pm Dw.mult) (φ : CR Dw.mult (A.V b) →+* L) (i : Fin (Dw.mult σ)),
      (fun r => φ (uvec (A.cv b) w ⟨σ, i⟩ r)) =
        ((A.A b).map (φ.comp (cC A b))).mulVec (((uC A b w σ).map φ).mulVec (Pi.single i 1)) := by
    intro b w φ i
    funext r
    rw [uvec_cv, Matrix.mulVec_single_one]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, map_sum]
  let av : Fin (Dw.mult σ) → L := ∑ l, f l • Pi.single (Fin.castLE hj l) 1
  have hq : (fun s => ψ' (uC A k'.1 k'.2 σ s j)) = ((uC A k'.1 k'.2 σ).map ψ').mulVec (Pi.single j 1) := by
    funext s
    rw [Matrix.mulVec_single_one]
    rfl
  have hL : ∑ l, f l • cv l = ((A.A k.1).map (ψ.comp (cC A k.1))).mulVec (((uC A k.1 k.2 σ).map ψ).mulVec av) := by
    simp only [cv, av, Matrix.mulVec_sum, Matrix.mulVec_smul]
    refine Finset.sum_congr rfl fun l _ => ?_
    exact congrArg _ (hcol k.1 k.2 ψ (Fin.castLE hj l))
  have hR : cv' (Fin.last j.1) = (a0 : L) • ((A.A k.1).map (ψ.comp (cC A k.1))).mulVec
      (Chx.mulVec (fun s => ψ' (uC A k'.1 k'.2 σ s j))) := by
    have e : Fin.castLE hj (Fin.last j.1) = j := Fin.ext rfl
    have := hcol k'.1 k'.2 ψ' j
    rw [← hq, ha0, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec] at this
    simp only [cv', std, e]
    exact this
  have hCA : (A.C k.1).map (ψ.comp (cC A k.1)) * (A.A k.1).map (ψ.comp (cC A k.1)) = 1 := by
    rw [← Matrix.map_mul, A.CA, Matrix.map_one _ (map_zero _) (map_one _)]
  have hC : ∀ v, ((A.C k.1).map (ψ.comp (cC A k.1))).mulVec (((A.A k.1).map (ψ.comp (cC A k.1))).mulVec v) = v :=
    fun v => by rw [Matrix.mulVec_mulVec, hCA, Matrix.one_mulVec]
  have key := congrArg ((A.C k.1).map (ψ.comp (cC A k.1))).mulVec (hf.trans hR)
  rw [hL, Matrix.mulVec_smul, hC, hC] at key
  refine ⟨((a0⁻¹ : Lˣ) : L) • av, fun i hi => ?_, ?_⟩
  · simp only [av, Pi.smul_apply, Finset.sum_apply, Pi.single_apply, smul_eq_mul]
    rw [Finset.sum_eq_zero fun l _ => ?_, mul_zero]
    rw [if_neg, mul_zero]
    intro h
    have := congrArg Fin.val h
    simp only [Fin.coe_castLE] at this
    have := l.2
    omega
  · rw [Matrix.mulVec_smul, key, smul_smul, Units.inv_mul, one_smul]

theorem isReduced_of_cells (hZ : Cells A π g κ) : IsReduced Z := by
  have : ∀ x : Z, _root_.IsReduced (Z.presheaf.stalk x) := fun x => by
    have := (hZ.normal x).1
    infer_instance
  exact isReduced_of_isReduced_stalk _

theorem flagCells_frames_triangular_common (hZ : Cells A π g κ) : FlagCellFrameChangeTriangular hZ := by
  haveI := isReduced_of_cells hZ
  intro k k' σ
  have hle : (κ k.1 k.2).opensRange ⊓ (κ k'.1 k'.2).opensRange ≤ π ⁻¹ᵁ ((A.k k.1).M.U ⊓ (A.k k'.1).M.U) :=
    inf_le_inf (cell_le hZ k) (cell_le hZ k')
  let Cm := (chg (A.k k.1).M.toMChart (A.k k'.1).M.toMChart).map
    (π.appLE ((A.k k.1).M.U ⊓ (A.k k'.1).M.U) ((κ k.1 k.2).opensRange ⊓ (κ k'.1 k'.2).opensRange) hle).hom
  let U' := ((uC A k'.1 k'.2 σ).map (cellθ κ k')).map (resG Z (inf_le_right :
    (κ k.1 k.2).opensRange ⊓ (κ k'.1 k'.2).opensRange ≤ _))
  let U := ((uC A k.1 k.2 σ).map (cellθ κ k)).map (resG Z (inf_le_left :
    (κ k.1 k.2).opensRange ⊓ (κ k'.1 k'.2).opensRange ≤ _))
  let Wm := ((wC A k.1 k.2 σ).map (cellθ κ k)).map (resG Z (inf_le_left :
    (κ k.1 k.2).opensRange ⊓ (κ k'.1 k'.2).opensRange ≤ _))
  have hWU : Wm * U = 1 := by
    simp only [Wm, U]
    rw [← Matrix.map_mul, ← Matrix.map_mul, wC_mul_uC, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.map_one _ (map_zero _) (map_one _)]
  have key : ∀ (L : Type) [Field L] (z : Sp L ⟶ Z)
      (hz : ⊤ ≤ z ⁻¹ᵁ ((κ k.1 k.2).opensRange ⊓ (κ k'.1 k'.2).opensRange)),
      (Cm * U').map (ev z _ hz) = U.map (ev z _ hz) * (Wm * (Cm * U')).map (ev z _ hz) ∧
        ∀ i j, j < i → (Wm * (Cm * U')).map (ev z _ hz) i j = 0 := by
    intro L _ z hz
    have hz1 := le_preimage_mono inf_le_left hz
    have hz2 := le_preimage_mono inf_le_right hz
    have hM := le_preimage_map π hle hz
    have eC : Cm.map (ev z _ hz) = (chg (A.k k.1).M.toMChart (A.k k'.1).M.toMChart).map (ev (z ≫ π) _ hM) := by
      ext r s
      exact ev_appLE z π hle hz hM _
    have eU : U.map (ev z _ hz) = (uC A k.1 k.2 σ).map ((ev z _ hz1).comp (cellθ κ k).toRingHom) := by
      ext r s
      exact ev_res z _ hz hz1 _
    have eU' : U'.map (ev z _ hz) = (uC A k'.1 k'.2 σ).map ((ev z _ hz2).comp (cellθ κ k').toRingHom) := by
      ext r s
      exact ev_res z _ hz hz2 _
    have h := tri_of_cols (U.map (ev z _ hz)) (Wm.map (ev z _ hz))
      (by rw [← Matrix.map_mul, hWU, Matrix.map_one _ (map_zero _) (map_one _)]) ((Cm * U').map (ev z _ hz))
      (fun j => by
        obtain ⟨a, ha, e⟩ := col_tri hZ k k' σ z hz1 hz2 hM j
        refine ⟨a, ha, ?_⟩
        rw [eU, ← e, Matrix.map_mul, eC, eU']
        funext r
        simp [Matrix.mul_apply, Matrix.mulVec, dotProduct])
    rw [show (Wm * (Cm * U')).map (ev z _ hz) = Wm.map (ev z _ hz) * (Cm * U').map (ev z _ hz) from Matrix.map_mul]
    exact h
  refine ⟨Wm * (Cm * U'), fun i j hij => ext_ev_field fun L _ z hz => ?_, ?_⟩
  · rw [map_zero]
    exact (key L z hz).2 i j hij
  · ext r s
    refine ext_ev_field fun L _ z hz => ?_
    have := congrFun (congrFun (key L z hz).1 r) s
    rw [← Matrix.map_mul] at this
    exact this

end GlobalTheory.FlagMod.FieldFlag

open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)

theorem GlobalTheory.FlagMod.FieldFlag.flagCells_frames_triangular : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) (A : Atlas Y p) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (g : ∀ en : En Dw.mult, Z ⟶ PSpace c.F (plN A.N en.1)) (κ : ∀ b, Pm Dw.mult → (Sp (CR Dw.mult (A.V b)) ⟶ Z)) [∀ b w, IsOpenImmersion (κ b w)] (hZ : Cells A π g κ), FlagCellFrameChangeTriangular hZ :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hZ => GlobalTheory.FlagMod.FieldFlag.flagCells_frames_triangular_common hZ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFrameApply
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogKSDiv

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}


open Classical in
def flatFrame {K : Type} [CommRing K] (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K) {n n' : ℕ}
    (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (e' : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n') :
    Matrix (Fin n) (Fin n') K :=
  (Matrix.blockDiagonal' A).submatrix e.symm e'.symm

theorem flatFrame_apply {K : Type} [CommRing K] (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K)
    {n n' : ℕ} (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (e' : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n')
    (τ : E →+* ℂ) (i k : Fin (Dw.mult τ)) : flatFrame A e e' (e ⟨τ, i⟩) (e' ⟨τ, k⟩) = A τ i k := by
  simp [flatFrame, Matrix.blockDiagonal'_apply_eq]

end GlobalTheory.LogKSDiv
end
end

