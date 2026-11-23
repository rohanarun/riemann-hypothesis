module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqZeroOfCobOneEqZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1852
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionHeightLowerBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1905
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1888
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1924
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2066
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyRestrictBasisExtendedBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2125
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1302
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0518

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalRigidifiedExtensionDeRhamClassAddSmul
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PtExt

variable {R : Type} [CommRing R]

section Basic

variable {X : Over (Sp R)} (f f' : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))) (r : R)

theorem fv_add_apply (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D']
    (φ : D →ₐ[R] D') (x : Pt X D) : fv (f + f') D D' φ x = fv f D D' φ x + fv f' D D' φ x := rfl

theorem fv_smul_apply (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D']
    (φ : D →ₐ[R] D') (x : Pt X D) : fv (r • f) D D' φ x = r • fv f D D' φ x := rfl

theorem cotVal_add_apply {D : Type} [CommRing D] [Bialgebra R D] (y : Pt X D) :
    cotVal (f + f') y = cotVal f y + cotVal f' y := by
  unfold cotVal
  simp only [fv_add_apply, map_add (f := _), map_sub]
  abel

theorem cotVal_smul_apply {D : Type} [CommRing D] [Bialgebra R D] (y : Pt X D) :
    cotVal (r • f) y = r • cotVal f y := by
  unfold cotVal
  simp only [fv_smul_apply, map_smul, map_sub, smul_sub]

end Basic

variable {A : Over (Sp R)} [GrpObj A] {p : ℕ} {G : PDivGroup p R} {t : G.TorsionTower A} {c c' : primDR A}

def Dat.sum (d : Dat t c) (d' : Dat t c') : Dat t (c + c') where
  f := d.f + d'.f
  cl := by rw [map_add (f := _), d.cl, d'.cl]; rfl
  g := fun D _ _ x y ↦ d.g D x y + d'.g D x y
  add := fun D _ _ D' _ _ φ x y ↦ by
    have h := d.add D D' φ x y
    have h' := d'.add D D' φ x y
    simp only [fv_add_apply, map_add (f := _)]
    linear_combination h + h'
  h := fun n ↦ d.h n + d'.h n
  res := fun n ↦ by
    have h := d.res n
    have h' := d'.res n
    simp only [fv_add_apply, map_add (f := _)]
    linear_combination h + h'

def Dat.scale (r : R) (d : Dat t c) : Dat t (r • c) where
  f := r • d.f
  cl := by rw [map_smul, d.cl]; rfl
  g := fun D _ _ x y ↦ r • d.g D x y
  add := fun D _ _ D' _ _ φ x y ↦ by
    have h := d.add D D' φ x y
    simp only [fv_smul_apply, map_smul]
    rw [← smul_sub, h, smul_sub, smul_sub]
  h := fun n ↦ r • d.h n
  res := fun n ↦ by
    have h := d.res n
    simp only [fv_smul_apply, map_smul]
    rw [← smul_sub, h]

theorem Dat.coc_sum (d : Dat t c) (d' : Dat t c') (n : ℕ) : (d.sum d').coc n = d.coc n + d'.coc n := by
  simp only [Dat.coc, Dat.sum, fv_add_apply, map_add (f := _)]
  abel

theorem Dat.om_sum (d : Dat t c) (d' : Dat t c') (n : ℕ) : (d.sum d').om n = d.om n + d'.om n := by
  simp only [Dat.om, Dat.sum, cotVal_add_apply, map_add (f := _)]
  abel

theorem Dat.coc_scale (r : R) (d : Dat t c) (n : ℕ) : (d.scale r).coc n = r • d.coc n := by
  simp only [Dat.coc, Dat.scale, fv_smul_apply, map_smul, smul_sub]

theorem Dat.om_scale (r : R) (d : Dat t c) (n : ℕ) : (d.scale r).om n = r • d.om n := by
  simp only [Dat.om, Dat.scale, cotVal_smul_apply, map_smul, smul_sub]

theorem isCan_add_smul (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R)
    (t : G.TorsionTower A) :
    (∀ (c c' : primDR A) (x x' : G.RigExt),
      IsCan t c x → IsCan t c' x' → IsCan t (c + c') (x + x')) ∧
    (∀ (r : R) (c : primDR A) (x : G.RigExt), IsCan t c x → IsCan t (r • c) (r • x)) := by
  constructor
  · rintro c c' _ _ ⟨d, z, w, hz, hw, rfl⟩ ⟨d', z', w', hz', hw', rfl⟩
    refine ⟨d.sum d', z + z', w + w', fun n ↦ ?_, fun n ↦ ?_, (map_add G.rigMk _ _).symm⟩
    · rw [Dat.coc_sum, ← hz, ← hz']; rfl
    · rw [Dat.om_sum, ← hw, ← hw']; rfl
  · rintro r c _ ⟨d, z, w, hz, hw, rfl⟩
    refine ⟨d.scale r, r • z, r • w, fun n ↦ ?_, fun n ↦ ?_, (map_smul G.rigMk r (z, w)).symm⟩
    · rw [Dat.coc_scale, ← hz]; rfl
    · rw [Dat.om_scale, ← hw]; rfl

end GlobalTheory.PtExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDivToWeilQDivisorAddOfEffective
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.QDivSum

theorem sum_eq : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → letI := algebraΓOfHom p; ∀ (D E : CartierDiv X) (a b : ℕ), 0 < a → 0 < b → D.Eff → E.Eff → (b • D + a • E).Eff ∧ qWeil (b • D + a • E) (a * b) = qWeil D a + qWeil E b ∧ ∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![toLB (b • D + a • E)] : ℚ) / ((a * b : ℕ) : ℚ) = (interNumRed ℂ C ![toLB D] : ℚ) / a + (interNumRed ℂ C ![toLB E] : ℚ) / b := by
  intro X _ _ p hp
  letI := algebraΓOfHom p
  intro D E a b ha hb hD hE
  refine ⟨(BoundaryFibre.eff_nsmul hD b).add (BoundaryFibre.eff_nsmul hE a), ?_, ?_⟩
  · funext z
    simp only [qWeil, Pi.add_apply, CartierDiv.mult_add, SmallSecHeight.mult_nsmul]
    have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
    have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
    push_cast
    field_simp
  · intro C hC
    have e : cls (toLB (b • D + a • E)) (isLB_toLB _) = b • cls (toLB D) (isLB_toLB D) + a • cls (toLB E) (isLB_toLB E) := by
      rw [← toPic_apply, ← toPic_apply, ← toPic_apply, map_add (f := _), map_nsmul, map_nsmul]
    rw [interNumRed_of_cls_eq_nsmul_add ℂ X p hp _ _ _ (isLB_toLB _) (isLB_toLB D) (isLB_toLB E) b a C hC e]
    have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
    have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
    push_cast
    field_simp

end GlobalTheory.QDivSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDivisorPullbackSupportAndEffective
section
set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Discrepancy

set_option autoImplicit false in
open CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter in
private theorem unitAt_functionFieldMap_of_unitAt {X Y : Scheme} [IsIntegral X]
    [IsIntegral Y] (s : Y ⟶ X) [IsDominant s] {y : Y} {f : X.functionField}
    (hf : _root_.GlobalTheory.Cartier.UnitAt (s y) f) :
    _root_.GlobalTheory.Cartier.UnitAt y (_root_.GlobalTheory.functionFieldMap s f) := by
  obtain ⟨a, hunit, ha⟩ := hf
  exact ⟨ConcreteCategory.hom (s.stalkMap y) a, hunit.map _, by
    rw [← _root_.GlobalTheory.functionFieldMap_algebraMap, ha]⟩

set_option autoImplicit false in
open CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter in
private theorem regAt_functionFieldMap_of_regAt {X Y : Scheme} [IsIntegral X]
    [IsIntegral Y] (s : Y ⟶ X) [IsDominant s] {y : Y} {f : X.functionField}
    (hf : _root_.GlobalTheory.Cartier.RegAt (s y) f) :
    _root_.GlobalTheory.Cartier.RegAt y (_root_.GlobalTheory.functionFieldMap s f) := by
  obtain ⟨a, ha⟩ := hf
  exact ⟨ConcreteCategory.hom (s.stalkMap y) a, by
    rw [← _root_.GlobalTheory.functionFieldMap_algebraMap, ha]⟩


set_option autoImplicit false in
open CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter in
theorem _root_.GlobalTheory.Discrepancy.pullCart_supp_and_eff : ∀ (X Y : Scheme.{0}) [IsIntegral X]
    [IsIntegral Y] (s : Y ⟶ X) [IsDominant s] (D : _root_.GlobalTheory.Cartier.CartierDiv X),
    (∀ y : Y, y ∈ (_root_.GlobalTheory.Discrepancy.pullCart s D).supp →
      s y ∈ D.supp) ∧
    (D.Eff → (_root_.GlobalTheory.Discrepancy.pullCart s D).Eff) := by
  intro X Y _ _ s _ D
  refine ⟨fun y hy => ?_, fun hD => ?_⟩
  · obtain ⟨g, hg⟩ := D.exists_isEqn (s y)
    have hg' := _root_.GlobalTheory.Discrepancy.isEqn_pullCart s hg
    rw [hg'.mem_supp_iff] at hy
    rw [hg.mem_supp_iff]
    intro hunit
    exact hy (unitAt_functionFieldMap_of_unitAt s hunit)
  · rw [_root_.GlobalTheory.Cartier.CartierDiv.eff_iff] at hD ⊢
    intro y g' hg'
    obtain ⟨g, hg⟩ := D.exists_isEqn (s y)
    have hpull := _root_.GlobalTheory.Discrepancy.isEqn_pullCart s hg
    have hquot := (hpull.iff_unitAt).1 hg'
    have hreg : _root_.GlobalTheory.Cartier.RegAt y
        ((_root_.GlobalTheory.Discrepancy.fnPull s g : (Y.functionField)ˣ) : Y.functionField) :=
      regAt_functionFieldMap_of_regAt s (hD (s y) g hg)
    have hprod := hquot.regAt.mul hreg
    rwa [div_mul_cancel₀ _ (Units.ne_zero _)] at hprod

end GlobalTheory.Discrepancy
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechKodairaSpencerMatrixEqZeroOffConjBlocks
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

namespace GlobalTheory.LogPole

theorem ksMatrix_eq_zero_of_ne_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (D : LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U) (Θ : Matrix (Fin n) (Fin n) Γ(TF.Y.X, U.1)), LogKS.IsKS TF.Y.t (LogKS.interior TF.Y) U v D.1 Θ → ∀ a b, (e.symm a).1 ≠ conjEmb (e.symm b).1 → Θ a b = 0 := by
  intro E _ _ _ H Dw l Xo c TF U n e v hv D Θ hKS i k hik
  obtain ⟨htan, huq, heig⟩ := hv
  let A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(TF.Y.X, U.1) :=
    fun x => Matrix.diagonal fun j => algX TF.Y.s U.1 (embK c (e.symm j).1 x)
  have hA : ∀ x j, IsCombAtG TF.Y.t (LogKS.chart U) v (A x j) (v j ≫ (TF.Y.t.act.act x).left) := by
    intro x j
    have h := heig x (e.symm j).1 (e.symm j).2
    simp only [Sigma.eta, Equiv.apply_symm_apply] at h
    convert h using 2
    ext t
    simp [A, Matrix.diagonal_apply, Pi.single_apply, eq_comm]
  obtain ⟨e', he'⟩ := TF.logKS U n v A htan huq hA
  have hmem : Θ ∈ LogKS.balanced H.bar A := by
    rw [(he' D Θ).1 hKS]
    exact (e' D).2
  have hd := ((LogKS.mem_balanced_diagonal H.bar
    (fun j x => algX TF.Y.s U.1 (embK c (e.symm j).1 x)) Θ).1 hmem).2
  obtain ⟨x, hx⟩ : ∃ x : 𝓞 E, embK c (e.symm i).1 x ≠ embK c ((starRingEnd ℂ).comp (e.symm k).1) x := by
    by_contra hcon
    push_neg at hcon
    apply hik
    apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E))
    ext y
    have h := congrArg (fun z : c.F => (z : ℂ)) (hcon y)
    simpa [embK_coe, conjEmb] using h
  have hu : IsUnit (algX TF.Y.s U.1 (embK c (e.symm i).1 x) -
      algX TF.Y.s U.1 (embK c (e.symm k).1 (H.bar x))) := by
    rw [GlobalTheory.LogKSDiv.GenKSProof.embK_bar', ← map_sub]
    exact (IsUnit.mk0 _ (sub_ne_zero.2 hx)).map _
  exact hu.mul_right_eq_zero.1 (hd x i k)

end GlobalTheory.LogPole
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPairRestrictBaseChangeBijective
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs.PairExt

variable {X X' Y : Scheme.{0}}

theorem pair_point (φ : X' ⟶ X) (x : X') (U : X'.Opens) (hx : x ∈ U) :
    ∃ t : (Pair φ)ᵒᵖ, x ∈ ((pairFst φ).obj t).unop.1 ∧ ((pairFst φ).obj t).unop.1 ≤ U := by
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (x := φ.base x) (U := (⊤ : X.Opens)) trivial
  obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := U ⊓ φ ⁻¹ᵁ V) ⟨hx, hxV⟩
  exact ⟨Opposite.op ⟨(⟨W, hW⟩, ⟨V, hV⟩), fun y hy ↦ (hWU hy).2⟩, hxW, fun y hy ↦ (hWU hy).1⟩

theorem pair_point_two (φ : X' ⟶ X) (t₁ t₂ : (Pair φ)ᵒᵖ) (x : X') (U : X'.Opens) (hx : x ∈ U)
    (h₁ : x ∈ ((pairFst φ).obj t₁).unop.1) (h₂ : x ∈ ((pairFst φ).obj t₂).unop.1) :
    ∃ t₃ : (Pair φ)ᵒᵖ, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ x ∈ ((pairFst φ).obj t₃).unop.1 ∧
      ((pairFst φ).obj t₃).unop.1 ≤ U := by
  have h₁' : x ∈ t₁.unop.1.1.1 := h₁
  have h₂' : x ∈ t₂.unop.1.1.1 := h₂
  obtain ⟨V, hV, hxV, hVV⟩ := exists_isAffineOpen_mem_and_subset (x := φ.base x)
    (U := t₁.unop.1.2.1 ⊓ t₂.unop.1.2.1) ⟨t₁.unop.2 h₁', t₂.unop.2 h₂'⟩
  obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset (x := x)
    (U := U ⊓ φ ⁻¹ᵁ V ⊓ (t₁.unop.1.1.1 ⊓ t₂.unop.1.1.1)) ⟨⟨hx, hxV⟩, h₁', h₂'⟩
  let t₃ : Pair φ := ⟨(⟨W, hW⟩, ⟨V, hV⟩), fun y hy ↦ (hWU hy).1.2⟩
  refine ⟨Opposite.op t₃, ⟨(homOfLE ?_).op⟩, ⟨(homOfLE ?_).op⟩, hxW, fun y hy ↦ (hWU hy).1.1⟩
  · exact ⟨fun y hy ↦ (hWU hy).2.1, fun y hy ↦ (hVV hy).1⟩
  · exact ⟨fun y hy ↦ (hWU hy).2.2, fun y hy ↦ (hVV hy).2⟩

theorem triple_point (φ : X' ⟶ X) (ψ : X ⟶ Y) (x : X') (U : X'.Opens) (hx : x ∈ U) :
    ∃ t : (Triple φ ψ)ᵒᵖ, x ∈ ((cechTripleProjFirstThird φ ψ ⋙ pairFst (φ ≫ ψ)).obj t).unop.1 ∧
      ((cechTripleProjFirstThird φ ψ ⋙ pairFst (φ ≫ ψ)).obj t).unop.1 ≤ U := by
  obtain ⟨Z, hZ, hxZ, -⟩ := exists_isAffineOpen_mem_and_subset (x := ψ.base (φ.base x)) (U := (⊤ : Y.Opens)) trivial
  obtain ⟨V, hV, hxV, hVZ⟩ := exists_isAffineOpen_mem_and_subset (x := φ.base x) (U := ψ ⁻¹ᵁ Z) hxZ
  obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := U ⊓ φ ⁻¹ᵁ V) ⟨hx, hxV⟩
  exact ⟨Opposite.op ⟨(⟨W, hW⟩, ⟨V, hV⟩, ⟨Z, hZ⟩), fun y hy ↦ (hWU hy).2, fun y hy ↦ hVZ hy⟩, hxW,
    fun y hy ↦ (hWU hy).1⟩

theorem triple_point_two (φ : X' ⟶ X) (ψ : X ⟶ Y) (t₁ t₂ : (Triple φ ψ)ᵒᵖ) (x : X') (U : X'.Opens) (hx : x ∈ U)
    (h₁ : x ∈ ((cechTripleProjFirstThird φ ψ ⋙ pairFst (φ ≫ ψ)).obj t₁).unop.1)
    (h₂ : x ∈ ((cechTripleProjFirstThird φ ψ ⋙ pairFst (φ ≫ ψ)).obj t₂).unop.1) :
    ∃ t₃ : (Triple φ ψ)ᵒᵖ, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧
      x ∈ ((cechTripleProjFirstThird φ ψ ⋙ pairFst (φ ≫ ψ)).obj t₃).unop.1 ∧
      ((cechTripleProjFirstThird φ ψ ⋙ pairFst (φ ≫ ψ)).obj t₃).unop.1 ≤ U := by
  have h₁' : x ∈ t₁.unop.1.1.1 := h₁
  have h₂' : x ∈ t₂.unop.1.1.1 := h₂
  have hy₁ : φ.base x ∈ t₁.unop.1.2.1.1 := t₁.unop.2.1 h₁'
  have hy₂ : φ.base x ∈ t₂.unop.1.2.1.1 := t₂.unop.2.1 h₂'
  obtain ⟨Z, hZ, hxZ, hZZ⟩ := exists_isAffineOpen_mem_and_subset (x := ψ.base (φ.base x))
    (U := t₁.unop.1.2.2.1 ⊓ t₂.unop.1.2.2.1) ⟨t₁.unop.2.2 hy₁, t₂.unop.2.2 hy₂⟩
  obtain ⟨V, hV, hxV, hVV⟩ := exists_isAffineOpen_mem_and_subset (x := φ.base x)
    (U := t₁.unop.1.2.1.1 ⊓ t₂.unop.1.2.1.1 ⊓ ψ ⁻¹ᵁ Z) ⟨⟨hy₁, hy₂⟩, hxZ⟩
  obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset (x := x)
    (U := U ⊓ φ ⁻¹ᵁ V ⊓ (t₁.unop.1.1.1 ⊓ t₂.unop.1.1.1)) ⟨⟨hx, hxV⟩, h₁', h₂'⟩
  let t₃ : Triple φ ψ := ⟨(⟨W, hW⟩, ⟨V, hV⟩, ⟨Z, hZ⟩), fun y hy ↦ (hWU hy).1.2, fun y hy ↦ (hVV hy).2⟩
  refine ⟨Opposite.op t₃, ⟨(homOfLE ?_).op⟩, ⟨(homOfLE ?_).op⟩, hxW, fun y hy ↦ (hWU hy).1.1⟩
  · exact ⟨fun y hy ↦ (hWU hy).2.1, fun y hy ↦ (hVV hy).1.1, fun y hy ↦ (hZZ hy).1⟩
  · exact ⟨fun y hy ↦ (hWU hy).2.2, fun y hy ↦ (hVV hy).1.2, fun y hy ↦ (hZZ hy).2⟩

theorem extHom_of_id {R₀ : Type} [CommRing R₀] (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] {B : Type} [CommRing B]
    [Algebra R₀ B] (f : B →ₐ[R₀] B) (hf : ∀ b, f b = b) (y : R₁ ⊗[R₀] B) : extHom R₁ f y = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [hf]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem cechTripleRestrict_comp_pairRestrict {R₀ : Type} [CommRing R₀] (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (s' : X' ⟶ Sp R₀)
    (φ : X' ⟶ X) (ψ : X ⟶ Y) (c : CatCoh.H1 (ext R₁ (OAff s'))) :
    (extMap R₁ (cechTripleRestrictFirst φ ψ s')).pull1 ((extMap R₁ (pairRes φ s')).pull1 c) =
      (extMap R₁ (CoefMap.restrict (OAff s') (cechTripleProjFirstThird φ ψ ⋙ pairFst (φ ≫ ψ)))).pull1 c := by
  obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
  rw [CoefMap.pullCohomologyOne_class, CoefMap.pullCohomologyOne_class, CoefMap.pullCohomologyOne_class]
  refine congrArg _ (Subtype.ext ?_)
  funext T T' a
  exact extHom_of_id R₁ (coefHom (cechTripleRestrictFirst φ ψ s') T') (fun _ ↦ rfl) _

theorem pairRes_ext_bijective : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (X X' : Scheme.{0}) (s' : X' ⟶ Sp R₀) (φ : X' ⟶ X), (Function.Bijective (extMap R₁ (pairRes φ s')).pull1 ∧ Function.Bijective (extMap R₁ (pairRes φ s')).pull2) ∧ ∀ (Y : Scheme.{0}) (ψ : X ⟶ Y), Function.Injective (extMap R₁ (cechTripleRestrictFirst φ ψ s')).pull1 := by
  intro R₀ R₁ _ _ _ X X' s' φ
  have hp : Function.Bijective (extMap R₁ (pairRes φ s')).pull1 ∧ Function.Bijective (extMap R₁ (pairRes φ s')).pull2 :=
    _root_.GlobalTheory.Obs.BasisExt.restrict_ext_bijective R₀ R₁ X' s' _ (pairFst φ) (pair_point φ) (pair_point_two φ)
  refine ⟨hp, fun Y ψ x y e ↦ ?_⟩
  obtain ⟨x0, rfl⟩ := hp.1.2 x
  obtain ⟨y0, rfl⟩ := hp.1.2 y
  rw [cechTripleRestrict_comp_pairRestrict, cechTripleRestrict_comp_pairRestrict] at e
  rw [(_root_.GlobalTheory.Obs.BasisExt.restrict_ext_bijective R₀ R₁ X' s' _ _ (triple_point φ ψ) (triple_point_two φ ψ)).1.1 e]

end GlobalTheory.Obs.PairExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassifyingMapSymplecticLevelEquivariant
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover

noncomputable section

namespace GlobalTheory.HTSympCover

theorem exists_objMap_cancel_φ {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R}
    {N : ℕ} {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R}
    {o₁ : Obj b N s₁} {o₂ : Obj b N s₂} {o₃ : Obj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃}
    (m : ObjMap o₁ o₃ (f ≫ g)) (m₂ : ObjMap o₂ o₃ g) : ∃ m₁ : ObjMap o₁ o₂ f, m₁.φ ≫ m₂.φ = m.φ := by
  have w : m.φ ≫ o₃.A.hom = (o₁.A.hom ≫ f) ≫ g := by rw [m.cart.1.w, Category.assoc]
  set φ := m₂.cart.1.lift m.φ (o₁.A.hom ≫ f) w
  have hφ : φ ≫ m₂.φ = m.φ := m₂.cart.1.lift_fst _ _ _
  have hφ' : φ ≫ o₂.A.hom = o₁.A.hom ≫ f := m₂.cart.1.lift_snd _ _ _
  have n : IsGrpPullback o₁.A o₃.A (f ≫ g) (φ ≫ m₂.φ) := by rw [hφ]; exact m.cart
  obtain ⟨φ₂, sq⟩ := MapComp.exists_isSquare hφ'
  have e : m.φ₂ = φ₂ ≫ m₂.φ₂ := MapComp.isSquare_unique m.sq (hφ ▸ MapComp.isSquare_comp sq m₂.sq)
  have hact : ∀ c, (o₁.act.act c).left ≫ φ = φ ≫ (o₂.act.act c).left := by
    intro c
    apply m₂.cart.1.hom_ext
    · rw [Category.assoc, hφ, m.act, Category.assoc, m₂.act, ← Category.assoc, hφ]
    · rw [Category.assoc, hφ', ← Category.assoc, Over.w, Category.assoc, Over.w, hφ']
  have heta : ∀ y, (o₁.eta y).left ≫ φ = f ≫ (o₂.eta y).left := by
    intro y
    apply m₂.cart.1.hom_ext
    · rw [Category.assoc, hφ, m.eta, Category.assoc, Category.assoc, m₂.eta]
    · rw [Category.assoc, hφ', ← Category.assoc, Over.w, Category.assoc, Over.w]
      show 𝟙 _ ≫ f = f ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id]
  exact ⟨{ φ := φ
           φ₂ := φ₂
           cart := m₂.cart.cancel n hφ'
           sq := sq
           act := hact
           pol := LBIso.trans o₁.isLB (pull_isLB o₃.isLB _) (pull_isLB o₂.isLB _) m.pol
             (LBIso.symm (MapComp.lbIso_pull_comp m₂.pol φ₂ e))
           eta := heta }, hφ⟩

theorem classify_equivariant : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ)
  (X : Scheme.{0}) (s : X ⟶ Sp R) (s₁ : X ⟶ Sp (cycAway M)) (u : Obj b N s)
  (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over X) ⟶ u.A)), HarrisTaylorSymplecticLevelFamilyUniversalProperty b N h M s s₁ u lev →
  ∀ (ρ : sympSimGrp h M → (X ⟶ X)), SympActs s s₁ u lev ρ →
  ∀ (σ : sympSimGrp h M → (cycAway M →+* cycAway M)), (∀ a, ρ a ≫ s₁ = s₁ ≫ spMap (σ a)) →
  ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (Y : Over S) (t₁ : Y.left ⟶ Sp (cycAway M))
    (lu : (Fin h ⊕ Fin h → ℤ) → (Y ⟶ o.A)) (o' : Obj b N (Y.hom ≫ t)) (m : ObjMap o' o Y.hom)
    (lv' : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over Y.left) ⟶ o'.A)), (∀ a, (lv' a).left ≫ m.φ = (lu a).left) →
    (∀ a, IsSympLev o'.P h M (zetaAway M) (t₁ ≫ spMap (σ a)) (sympTwist a lv')) →
    ∀ (y : Y.left ⟶ X) (my : ObjMap o' u y), (∀ a, (lv' a).left ≫ my.φ = y ≫ (lev a).left) →
    y ≫ s = Y.hom ≫ t → y ≫ s₁ = t₁ →
    ∀ (r : sympSimGrp h M → (Y ⟶ Y)), (∀ a, (r a).left ≫ t₁ = t₁ ≫ spMap (σ a)) →
    (∀ a c, r a ≫ lu c = sympTwist a lu c) → ∀ a, (r a).left ≫ y = y ≫ ρ a := by
  intro p _ D R _ b N h M X s s₁ u lev hU ρ hρ σ hσ S t o Y t₁ lu o' m lv' hlv' hlev y my hmy hys hys₁ r hrt hr a
  let compObj : ∀ {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R}
      {o₁ : Obj b N s₁} {o₂ : Obj b N s₂} {o₃ : Obj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃},
      ObjMap o₁ o₂ f → ObjMap o₂ o₃ g → ObjMap o₁ o₃ (f ≫ g) := by
    intro S₁ S₂ S₃ s₁ s₂ s₃ o₁ o₂ o₃ f g m₁ m₂
    exact { φ := m₁.φ ≫ m₂.φ
            φ₂ := m₁.φ₂ ≫ m₂.φ₂
            cart := m₁.cart.comp m₂.cart
            sq := MapComp.isSquare_comp m₁.sq m₂.sq
            act := fun c => by rw [← Category.assoc, m₁.act, Category.assoc, m₂.act, Category.assoc]
            pol := LBIso.trans o₁.isLB (pull_isLB o₂.isLB _) (pull_isLB o₃.isLB _) m₁.pol
              (MapComp.lbIso_pull_comp m₂.pol m₁.φ₂ rfl)
            eta := fun c => by rw [← Category.assoc, m₁.eta, Category.assoc, m₂.eta, Category.assoc] }
  have cast : ∀ {f f' : Y.left ⟶ S} (_ : f = f') (m₀ : ObjMap o' o f), ∃ m' : ObjMap o' o f', m'.φ = m₀.φ := by
    intro f f' e m₀; subst e; exact ⟨m₀, rfl⟩
  have hrY : (r a).left ≫ Y.hom = Y.hom := Over.w (r a)
  obtain ⟨ma, hma⟩ := (hρ a).2.2

  have h₁ : (y ≫ ρ a) ≫ s = Y.hom ≫ t ∧ (y ≫ ρ a) ≫ s₁ = t₁ ≫ spMap (σ a) ∧
      ∃ m' : ObjMap o' u (y ≫ ρ a), ∀ c, (sympTwist a lv' c).left ≫ m'.φ = (y ≫ ρ a) ≫ (lev c).left := by
    refine ⟨by rw [Category.assoc, (hρ a).1, hys], by rw [Category.assoc, hσ, ← Category.assoc, hys₁],
      compObj my ma, fun c => ?_⟩
    have e₁ := hmy (liftMod ((a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) (reduceMod M c)))
    have e₂ := hma c
    simp only [sympTwist] at e₂ ⊢
    dsimp [compObj]
    change _ ≫ my.φ ≫ ma.φ = _
    rw [← Category.assoc, e₁, Category.assoc, e₂, Category.assoc]

  obtain ⟨mr, hmr⟩ := cast hrY.symm m
  obtain ⟨m₂, hφ⟩ := exists_objMap_cancel_φ mr m
  rw [hmr] at hφ
  have hpull : ∀ c, (sympTwist a lv' c).left ≫ m₂.φ = (r a).left ≫ (lv' c).left := by
    intro c
    apply m.cart.1.hom_ext
    · rw [Category.assoc, hφ, Category.assoc, hlv' c]
      simp only [sympTwist] at hlv' ⊢
      rw [hlv', ← Over.comp_left, hr a c]
      rfl
    · rw [Category.assoc, m₂.cart.1.w, ← Category.assoc, Over.w (sympTwist a lv' c), Category.assoc,
        Over.w (lv' c)]
      simp
  have h₂ : ((r a).left ≫ y) ≫ s = Y.hom ≫ t ∧ ((r a).left ≫ y) ≫ s₁ = t₁ ≫ spMap (σ a) ∧
      ∃ m' : ObjMap o' u ((r a).left ≫ y), ∀ c, (sympTwist a lv' c).left ≫ m'.φ = ((r a).left ≫ y) ≫ (lev c).left := by
    refine ⟨by rw [Category.assoc, hys, ← Category.assoc, hrY], by rw [Category.assoc, hys₁, hrt],
      compObj m₂ my, fun c => ?_⟩
    dsimp [compObj]
    change _ ≫ m₂.φ ≫ my.φ = _
    rw [← Category.assoc, hpull c, Category.assoc, hmy c, Category.assoc]
  exact (hU Y.left (Y.hom ≫ t) (t₁ ≫ spMap (σ a)) o' (sympTwist a lv') (hlev a)).unique h₂ h₁

end GlobalTheory.HTSympCover
end
end

