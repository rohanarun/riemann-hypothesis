module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import ReciprocityTheory.Automorphisms.Unitary
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.LocusEqTopOfDualPow
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsIsoGrCechMapPolyToGamma

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.InstCMHostS
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.IndefR Formalism.IndefR.principalLevelFrame
open scoped TensorProduct

namespace GlobalTheory.StdFrame

attribute [local instance] Formalism.BasicNotions.Host.cmStar

local instance instCMHostS (D : Formalism.BasicNotions.D7) : IsCMField D.host.E := D.host.isCMField_hostE

def tensCastR {E : Type} [Field E] [NumberField E] {F1 F2 : Subfield E} (h : F1 = F2) :
    FiniteAdeleRing (𝓞 F1) F1 ⊗[F1] E ≃+* E ⊗[F2] FiniteAdeleRing (𝓞 F2) F2 := by
  subst h
  exact (Algebra.TensorProduct.comm F1 (FiniteAdeleRing (𝓞 F1) F1) E).toRingEquiv

variable {D : D7}

def StdPsi {V : HSp D} {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (P : RowPsi V n) : Prop :=
  (∃ (β : Matrix (Fin V.rank) (Fin n) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E))
      (β' : Matrix (Fin n) (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)),
      β * β' = 1 ∧ β' * β = 1 ∧
      ∀ κ, finMat D.sp.cm.sig V.gram (P.ψ κ) =
        β * ((κ.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL D.host.E)).map (tensCastR hF).symm) * β') ∧
  ∀ κ, κ ∈ ReciprocityTheory.Aut.Umax D.host.E n ↔ P.ψ κ ∈ KsphC V ∅

end GlobalTheory.StdFrame

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsPow8F
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.LieHt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow

def IsPow8 {S : Scheme.{0}} (P P₈ : PolAV S) (d : ℕ) (pr : Fin 8 → (P₈.A ⟶ P.A)) (inc : P.A ⟶ P₈.A) : Prop :=
  (∀ u, IsMonHom (pr u)) ∧ IsMonHom inc ∧ (∀ (T : Over S) (y : Fin 8 → (T ⟶ P.A)), ∃! x : T ⟶ P₈.A, ∀ u, x ≫ pr u = y u) ∧
    (∀ u, inc ≫ pr u = if u = 0 then 𝟙 P.A else 1) ∧ LBIso (P₈.L.pull inc.left) (lbPow P.L d)

end GlobalTheory.MBLow

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.KeyPBIff
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KeyCl GlobalTheory.Ex
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow

def KeyAtMap {R R' : Type} [CommRing R] [CommRing R'] (x' : KeyIn R') (x : KeyIn R) (f : R →+* R')
    (φ : x'.P.A.left ⟶ x.P.A.left) : Prop :=
  ∃ (he : eSec x'.P.A ≫ φ = spMap f ≫ eSec x.P.A)
    (w : LB.Iso x'.P.L (x.P.L.pull φ)) (hg : x'.P.g = x.P.g) (F : DualNumber R →+* DualNumber R'),
    IsGrpPullback x'.P.A x.P.A (spMap f) φ ∧ w.IsGen ∧
    LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec x'.P.A) (fun _ => 1)) x'.rig
      (rigPullOf φ (spMap f) he x.P.L x.rig) ∧
    (∀ (j : (x.P.L.pull φ).ι) (i : x'.P.L.ι)
      (h : (x.P.L.pull φ).U j ⊓ x'.P.L.U i ≤ φ ⁻¹ᵁ x.P.L.U (j PUnit.unit)),
      (φ.appLE _ _ h).hom (x.th.f (j PUnit.unit)) =
        (show Γ(x'.P.A.left, (x.P.L.pull φ).U j ⊓ x'.P.L.U i) from (w.s (j, i)).val) *
          resG _ inf_le_right (x'.th.f i)) ∧
    (∀ a, F (algebraMap R _ a) = algebraMap R' _ (f a)) ∧ F DualNumber.eps = DualNumber.eps ∧
    ∀ i, (x'.v i).left ≫ φ = spMap F ≫ (x.v (i.cast hg)).left

end GlobalTheory.MBLow

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.PointSide
section
noncomputable section

open scoped Classical

namespace GlobalTheory.LKCount

section Vol

variable {G : Type} [Group G]

def vol (C H : Subgroup G) : ℚ := ((C.relIndex H : ℕ) : ℚ) / ((H.relIndex C : ℕ) : ℚ)

def orbC (θ : G →* G) (K C : Subgroup G) (δ : G) (f : G → ℂ) : ℂ :=
  ∑ᶠ q : DoubleCoset.Quotient (GlobalTheory.BCT.twCent θ δ : Set G) (K : Set G),
    ((vol C (GlobalTheory.BCT.twCent θ δ ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom) : ℚ) : ℂ)⁻¹ *
      f ((Quotient.out q)⁻¹ * δ * θ (Quotient.out q))

def orbK (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ) : ℂ :=
  orbC θ K (GlobalTheory.BCT.twCent θ δ ⊓ K) δ f

def massC (Γ' T C : Subgroup G) : ℚ :=
  ∑ᶠ q : DoubleCoset.Quotient ((Γ'.subgroupOf T : Subgroup T) : Set T) ((C.subgroupOf T : Subgroup T) : Set T),
    ((Nat.card ((Γ'.subgroupOf T) ⊓ (C.subgroupOf T).map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup T) : ℕ) : ℚ)⁻¹

end Vol

section Count

variable {Γ G₁ G₂ : Type} [Group Γ] [Group G₁] [Group G₂]

def stab (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (x : G₁ × G₂) : Subgroup Γ :=
  (K₁.map (MulAut.conj x.1).toMonoidHom).comap ι₁ ⊓ (K₂.map (MulAut.conj x.2).toMonoidHom).comap ι₂

def pointSum (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (θ : G₂ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (γ : G₁) (δ : G₂)
    (f₁ : G₁ → ℂ) (φ : G₂ → ℂ) : ℂ :=
  ∑ᶠ q : DoubleCoset.Quotient ((ι₁.prod ι₂).range : Set (G₁ × G₂)) ((K₁.prod K₂ : Subgroup (G₁ × G₂)) : Set (G₁ × G₂)),
    ((Nat.card (stab ι₁ ι₂ K₁ K₂ (Quotient.out q)) : ℕ) : ℂ)⁻¹ *
      (f₁ ((Quotient.out q).1⁻¹ * γ * (Quotient.out q).1) * φ ((Quotient.out q).2⁻¹ * δ * θ (Quotient.out q).2))

def pointSide (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (θ : G₂ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (γ : G₁) (δ : G₂)
    (f₁ : G₁ → ℂ) (φ : G₂ → ℂ) : ℂ :=
  ((massC (ι₁.prod ι₂).range (GlobalTheory.BCT.twCent ((MonoidHom.id G₁).prodMap θ) (γ, δ))
      (GlobalTheory.BCT.twCent ((MonoidHom.id G₁).prodMap θ) (γ, δ) ⊓ K₁.prod K₂) : ℚ) : ℂ) *
    (orbK (MonoidHom.id G₁) K₁ γ f₁ * orbK θ K₂ δ φ)

def term (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (θ : G₂ →* G₂) (δ : G₂) (f₁ : G₁ → ℂ) (φ : G₂ → ℂ) (x : G₁ × G₂) (γ : Γ) : ℂ :=
  f₁ (x.1⁻¹ * ι₁ γ * x.1) * φ (x.2⁻¹ * (ι₂ γ * δ) * θ x.2)

def centSum (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (θ : G₂ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (δ : G₂)
    (f₁ : G₁ → ℂ) (φ : G₂ → ℂ) (γ : Γ) : ℂ :=
  ∑ᶠ q : DoubleCoset.Quotient (((Subgroup.centralizer {γ}).map (ι₁.prod ι₂) : Subgroup (G₁ × G₂)) : Set (G₁ × G₂))
      ((K₁.prod K₂ : Subgroup (G₁ × G₂)) : Set (G₁ × G₂)),
    ((Nat.card (stab ι₁ ι₂ K₁ K₂ (Quotient.out q) ⊓ Subgroup.centralizer {γ} : Subgroup Γ) : ℕ) : ℂ)⁻¹ *
      term ι₁ ι₂ θ δ f₁ φ (Quotient.out q) γ

end Count

section Examples

end Examples

end GlobalTheory.LKCount
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.ShiftTw
section
noncomputable section

namespace GlobalTheory.LKRes

variable {H : Type} [Group H]

def conv (K : Subgroup H) (f f' : H → ℂ) (x : H) : ℂ :=
  ∑ᶠ q : H ⧸ K, f (Quotient.out q) * f' ((Quotient.out q)⁻¹ * x)

end GlobalTheory.LKRes
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.SmoothOfRelativeDimensionPspace
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Adelic

open CategoryTheory _root_.CategoryTheory.Limits AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.Points GlobalTheory.Twist GlobalTheory.ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

theorem isStandardSmooth_mvPolynomial (R σ : Type) [CommRing R] [Finite σ] :
    Algebra.IsStandardSmoothOfRelativeDimension (Nat.card σ) R (MvPolynomial σ R) := by
  let P₀ : Algebra.Presentation R (MvPolynomial σ R) σ Empty :=
    { __ := Algebra.Generators.mvPolynomial R σ
      relation := Empty.elim
      span_range_relation_eq_ker := by
        rw [Algebra.Generators.ker_mvPolynomial]
        simp }
  let P₁ : Algebra.PreSubmersivePresentation R (MvPolynomial σ R) σ Empty :=
    { __ := P₀
      map := Empty.elim
      map_inj := fun a => a.elim }
  let P₂ : Algebra.SubmersivePresentation R (MvPolynomial σ R) σ Empty :=
    { __ := P₁
      jacobian_isUnit := by
        rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
        simp }
  exact P₂.isStandardSmoothOfRelativeDimension (by simp [Algebra.Presentation.dimension])

theorem smoothOfRelativeDimension_pspace (R : Type) [CommRing R] (M : ℕ) :
    SmoothOfRelativeDimension M (PSpace.str R M) := by
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @SmoothOfRelativeDimension.{0} M)
    (Q := RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension M))
  refine IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension.{0} M) (chartCover R M)
    fun (i : Fin (M + 1)) => ?_
  change SmoothOfRelativeDimension M (chartι R M i ≫ _)
  rw [chartι_str]
  refine (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension M)).2 ?_
  refine RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ ?_
  have h := isStandardSmooth_mvPolynomial R {j : Fin (M + 1) // j ≠ i}
  rw [show Nat.card {j : Fin (M + 1) // j ≠ i} = M by simp] at h
  exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap M).2 h

variable (k : Type) [Field k] (M : ℕ)

theorem geometricallyConnected_pspace : GeometricallyConnected (PSpace.str k M) :=
  ⟨geometrically_iff_of_commRing.2 fun K _ _ _ _ _ h =>
    have e := (isPullback_baseChange M (algebraMap k K)).isoIsPullback _ _ h
    e.hom.homeomorph.surjective.connectedSpace e.hom.continuous⟩

abbrev projSys : LinSys k where
  Y := PSpace k M
  str := PSpace.str k M
  D := M
  L := O1 k M
  isLB := O1_isLB k M
  N := M + 1
  b := coord k M

namespace projSys

theorem algebraΓ_eq : (projSys k M).algebraΓ = algebraSections k M ⊤ :=
  Algebra.algebra_ext _ _ fun r => (LB.resG_self (X := PSpace k M) le_top _).symm

theorem isVariety (hM : 1 ≤ M) : (projSys k M).IsVariety :=
  ⟨smoothOfRelativeDimension_pspace k M, ⟨M, 𝟙 _, inferInstance, Category.id_comp _⟩,
    geometricallyConnected_pspace k M, hM⟩

theorem basePointFree : (projSys k M).BasePointFree := iSup_nonzeroLocus_coord k M

theorem form_eq {d : ℕ} {g : MvPolynomial (Fin (M + 1)) k} (hg : g.IsHomogeneous d) :
    (projSys k M).form hg = ProjSpace.formSec d g hg := by
  rw [ProjCoh.formSec_eq]
  exact congrArg (fun a : Algebra k Γ(PSpace k M, ⊤) =>
    letI := a; Twist.formSec (coord k M) (mem_polyGrading_natCast.2 hg)) (algebraΓ_eq k M)

theorem del_eq_one : (projSys k M).del = 1 := by
  have h := interNum_const_of_polynomial k (structureModule (PSpace k M)) (O1_isLB k M) (d := M)
    (Polynomial.preHilbertPoly ℚ M 0) (Polynomial.natDegree_preHilbertPoly ℚ M 0).le
    (ProjCoh.chi_sheafO_eq_eval k M)
  rw [Polynomial.coeff_preHilbertPoly_self, mul_inv_cancel₀ (Nat.cast_ne_zero.2 M.factorial_ne_zero)] at h
  rw [LinSys.del, algebraΓ_eq]
  exact_mod_cast h

theorem eq_of_sameImage {y y' : PSpace k M} (h : (projSys k M).SameImage y y') : y = y' := by
  refine ProjectiveSpectrum.ext (HomogeneousIdeal.ext' fun d g hg => ?_)
  replace hg : g.IsHomogeneous d := hg
  have := h d g hg
  rw [form_eq, nonzeroLocus_formSec] at this
  exact not_iff_not.1 this

theorem noContract (bd : Set (PSpace k M)) : (projSys k M).NoContract bd := fun C _ _ hC _ h => by
  have : Subsingleton C := ⟨fun a b => Subtype.ext (eq_of_sameImage k M (h _ a.2 _ b.2))⟩
  have := topologicalKrullDim_zero_of_discreteTopology C
  rw [hC] at this
  exact absurd this (by decide)

abbrev gen : PSpace k M := AmpleModel.genericPt k M

theorem gen_mem (i : Fin (M + 1)) : gen k M ∈ chart k M i := fun h => X_ne_zero (R := k) i h

theorem indep : (projSys k M).Indep := fun u hu => by
  have hg : (∑ j, C (u j) * X j : MvPolynomial (Fin (M + 1)) k).IsHomogeneous 1 :=
    IsHomogeneous.sum _ _ _ fun j _ => (isHomogeneous_X k j).C_mul _
  have h0 : (∑ j, C (u j) * X j : MvPolynomial (Fin (M + 1)) k) = 0 := by
    by_contra hne
    have h1 : ptOf (resPt (gen k M)) ∈ nonzeroLocus ((projSys k M).form hg) := by
      rw [ptOf_resPt, form_eq, nonzeroLocus_formSec]
      exact hne
    refine ((projSys k M).powVal_ne_zero_iff _ _).2 h1 ?_
    have h2 := (projSys k M).val_comb (resPt (gen k M)) u
    rw [hu, LinSys.val_zero] at h2
    rw [LinSys.powVal_form, h2, eval₂_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [eval₂_mul, eval₂_C, eval₂_X]
  funext j
  have := congrArg (eval (Pi.single j 1 : Fin (M + 1) → k)) h0
  simpa [Pi.single_apply] using this

theorem valR_resPt {Y : Scheme.{0}} (y : Y) (U : Y.Opens) (hy : y ∈ U) (f : Γ(Y, U)) :
    valR (resPt y) U f = Y.evaluation U y hy f := by
  have ht : ⊤ ≤ Y.fromSpecStalk y ⁻¹ᵁ U := (le_preimage_iff (C := Y.presheaf.stalk y) _ U).2 (by
    rw [show Y.fromSpecStalk y (IsLocalRing.closedPoint (Y.presheaf.stalk y)) = y from
      Scheme.fromSpecStalk_closedPoint]; exact hy)
  have e : valMap (C := Y.presheaf.stalk y) (Y.fromSpecStalk y) U ht = Y.presheaf.germ U y hy := by
    change (Y.fromSpecStalk y).appLE U ⊤ ht ≫ (Scheme.ΓSpecIso (Y.presheaf.stalk y)).hom = _
    rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hy]
    simp only [Category.assoc]
    have e : (Spec (Y.presheaf.stalk y)).presheaf.map (homOfLE (le_top : Y.fromSpecStalk y ⁻¹ᵁ U ≤ ⊤)).op ≫
        (Spec (Y.presheaf.stalk y)).presheaf.map (homOfLE ht).op = 𝟙 _ := by
      rw [← Functor.map_comp]; exact CategoryTheory.Functor.map_id _ _
    rw [reassoc_of% e, Iso.inv_hom_id, Category.comp_id]
  exact (valR_spMap_comp (Y.residue y).hom (Y.fromSpecStalk y) U ht f).trans (congrArg (Y.residue y).hom
    ((valR_eq (C := Y.presheaf.stalk y) _ _ ht f).trans (congrArg (fun q => q.hom f) e)))

theorem birational : (projSys k M).Birational := by
  refine ⟨gen k M, ?_, eq_top_iff.2 fun r _ => ?_⟩
  · exact Set.eq_univ_of_forall fun x => (ProjectiveSpectrum.le_iff_mem_closure _ _ x).1
      (show ⊥ ≤ x.asHomogeneousIdeal from bot_le)
  have hx : ptOf (resPt (gen k M)) ∈ chart k M 0 := by rw [ptOf_resPt]; exact gen_mem k M 0
  have hx' := (le_iff_ptOf_mem _ _).2 hx
  obtain ⟨c, hc, h, -⟩ := (projSys k M).exists_frame_change (resPt (gen k M)) (0 : Fin (M + 1)) hx
  have key : ∀ f : Γ(PSpace k M, chart k M 0),
      valR (resPt (gen k M)) _ f ∈ (projSys k M).ratioField (resPt (gen k M)) := fun f => by
    obtain ⟨p, rfl⟩ := aeval_ratio_surjective k M 0 f
    induction p using MvPolynomial.induction_on with
    | C a =>
      refine Subfield.subset_closure (Or.inl ⟨a, ?_⟩)
      rw [algHom_C, ← resG_algebraMap le_top, ← algebraΓ_eq]
      exact ((valR_res _ le_top hx' _).trans ((projSys k M).valR_algebraMap _ a)).symm
    | add p q hp hq => rw [map_add (f := _), valR_add _ _ hx']; exact add_mem hp hq
    | mul_X p j hp =>
      rw [map_mul, valR_mul _ _ hx', aeval_X]
      refine mul_mem hp (Subfield.subset_closure (Or.inr ⟨j, (0 : Fin (M + 1)), ?_⟩))
      have h0 : 1 = c * (projSys k M).coords (resPt (gen k M)) (0 : Fin (M + 1)) :=
        (valR_one _ _ hx').symm.trans ((congrArg _ (ratioOn_self (hi := le_rfl)).symm).trans (h (coord k M 0)))
      rw [← mul_div_mul_left _ _ hc, ← h0, div_one]
      exact h (coord k M j)
  obtain ⟨t, rfl⟩ := (PSpace k M).residue_surjective _ r
  let := (PSpace k M).presheaf.algebra_section_stalk (U := chart k M 0) ⟨gen k M, gen_mem k M 0⟩
  have := (isAffineOpen_chart k M 0).isLocalization_stalk ⟨gen k M, gen_mem k M 0⟩
  obtain ⟨⟨a, s⟩, e⟩ := IsLocalization.surj
    ((isAffineOpen_chart k M 0).primeIdealOf ⟨gen k M, gen_mem k M 0⟩).asIdeal.primeCompl t
  have hs := (IsLocalization.map_units ((PSpace k M).presheaf.stalk (gen k M)) s).map
    ((PSpace k M).residue (gen k M)).hom
  have e' := congrArg ((PSpace k M).residue (gen k M)).hom e
  rw [map_mul, ← eq_div_iff hs.ne_zero] at e'
  have ha := key a
  have hb := key s
  rw [valR_resPt _ _ (gen_mem k M 0)] at ha hb
  exact e' ▸ div_mem ha hb

end projSys
end GlobalTheory.Adelic
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.TanRel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KeyCl GlobalTheory.Ex
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I} {A : PolAV (Sp (FractionRing R))}
  {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

def TanRel (U : UnifPre I D A G) (y : epsR R ⟶ G) (gm : GtPt D.toPre (epsR R)) : Prop :=
  ∀ e : ℕ, ∃ ye : Sp (DualNumber (R ⧸ I ^ (e + 1))) ⟶ (thickObj R I e G).left,
    ye ≫ (fstG I e G).left = spMap (dualMap (Ideal.Quotient.mk (I ^ (e + 1)))) ≫ y.left ∧
    ye ≫ (U.gt e).pG.left = spMap (dualMap (Ideal.Quotient.mk (I ^ (e + 1)))) ≫ gm.b.left ∧
    ∀ χ, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ye)
      (LB.pullGen D.toPre.P.L _ _ (gm.s χ) (spMap (dualMap (Ideal.Quotient.mk (I ^ (e + 1))))))

def GtTan {D₀ : DegPre R} (gm : GtPt D₀ (epsR R)) : Prop :=
  ∃ o : GtPt D₀ (baseOver (Sp R)), o.IsZero ∧ GtPt.IsPull (redE R) gm o

abbrev toF (R : Type) [CommRing R] [IsDomain R] (F : Type) [Field F] [Algebra (FractionRing R) F] : R →+* F :=
  (algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))

def VecAt (U : UnifPre I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (y : epsR R ⟶ G)
    (yA : Sp (DualNumber F) ⟶ (TFK (R := R) F ⊗ A.A).left) : Prop :=
  yA ≫ (fst (TFK (R := R) F) A.A).left = spMap (algebraMap F (DualNumber F)) ∧
  yA ≫ (snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) = spMap (dualMap (toF R F)) ≫ y.left

def ArchF (κ : Rule) : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R] (D : DegPre R), D.PsiEven → D.TauBimult →
    ∀ (F : Type) [Field F] [CharZero F] [Algebra (FractionRing R) F] (e : F ≃+* ℂ) (N : NumD F) (ν : NumOf D F N) (g r m k : ℕ),
    1 ≤ g → Odd m → m ^ 2 ∣ k →
    ∀ (β : N.Form k) (ζ : Fˣ) (q : (Fin (2 * g) → ZMod (m ^ 2)) → N.QT (m ^ 2)), QLevel N g (m ^ 2) ζ q →
    ∀ (s : (Fin (2 * g) → ZMod (m ^ 2)) → Fam D F (m ^ 2)), (∀ a, ∃ f, ν.FamV (s a) f ∧ IsEvFam N m (q a) f) →
    ∀ (vB : Fin D.P.g → (epsR R ⟶ D.P.A)) (bX : Module.Basis (Fin r) ℤ N.X) (σ : Fin g ≃ Fin D.P.g ⊕ Fin r)
      (gm : Fin g → GtPt D (TE R F)), Adapted ν vB bX σ gm → ∀ k₀ : F, BKey κ ν vB k₀ →
    ∃ ε : ℝ, 0 < ε ∧ ∀ u : ℂ, u ≠ 0 → ‖u‖ < ε →
      (∀ a j, (Summable fun α => ‖e ((jc ν (s a) (gm j) α).fst / ν.rg ^ (m ^ 2)) * u ^ (β.be α α / (2 * m ^ 2)).toNat‖) ∧
        Summable fun α => ‖e ((jc ν (s a) (gm j) α).snd / ν.rg ^ (m ^ 2)) * u ^ (β.be α α / (2 * m ^ 2)).toNat‖) ∧
      ∃ (x₀ : KeyIn ℂ) (hg₀ : x₀.P.g = g) (lev₀ : Out.Level x₀.P (m ^ 2) (unitOn (Units.map (e : F →+* ℂ).toMonoidHom ζ)))
        (ϑ : _ → ℂ),
        (∀ a j, ϑ a = ∑' α, e ((jc ν (s a) (gm j) α).fst / ν.rg ^ (m ^ 2)) * u ^ (β.be α α / (2 * m ^ 2)).toNat) ∧
        ThJet x₀ hg₀ m (levelPoint lev₀ hg₀) ϑ
          (fun a j => ∑' α, e ((jc ν (s a) (gm j) α).snd / ν.rg ^ (m ^ 2)) * u ^ (β.be α α / (2 * m ^ 2)).toNat) ∧
        (κ ℂ x₀ : ℂ) = e k₀

def AllV (P : ∀ {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {D : DegData V (IsLocalRing.maximalIdeal V)}
    {A : PolAV (Sp (FractionRing V))} {G : Over (Sp V)} [GrpObj G] [IsCommMonObj G],
    Unif (IsLocalRing.maximalIdeal V) D A G → Prop) : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
    IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (D : DegData V (IsLocalRing.maximalIdeal V))
    (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G →
    ∀ U : Unif (IsLocalRing.maximalIdeal V) D A G, P U

def AllVC (P : ∀ {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {D : DegData V (IsLocalRing.maximalIdeal V)}
    {A : PolAV (Sp (FractionRing V))} {G : Over (Sp V)} [GrpObj G] [IsCommMonObj G]
    (_ : Unif (IsLocalRing.maximalIdeal V) D A G) {C : Type} [NontriviallyNormedField C] [Algebra (FractionRing V) C]
    {N : NumD C}, NumOf D.toPre C N → Prop) : Prop :=
  AllV fun {V} _ _ _ {D} {_} {_} _ _ U =>
    ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C]
      [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C →
      ∀ (N : NumD C) (ν : NumOf D.toPre C N), ν.IntN → P U ν

end GlobalTheory.MBLow

end
end

