module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Formalism.HarderNarasimhan.StatementPl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1048
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0932
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0965
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0890
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0947
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0902
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0907
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0887
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1149
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0997
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0909
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0942
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopRankPowers
public import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiRegularAlongOfEtale
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSubPtsIffOfToBaseEq
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

namespace GlobalTheory.HSCore.SplitField

theorem exists_algHom_factor (E A : Type) [Field E] [CommRing A] [Algebra E A] [Module.Finite E A] :
    ∃ p : Polynomial E, ∀ (Ω : Type) [Field Ω] [Algebra E Ω] [Algebra p.SplittingField Ω]
      [IsScalarTower E p.SplittingField Ω] (φ : A →ₐ[E] Ω),
      ∃ φ₀ : A →ₐ[E] p.SplittingField, ∀ a, φ a = algebraMap p.SplittingField Ω (φ₀ a) := by
  classical
  obtain ⟨t, ht⟩ := Module.Finite.fg_top (R := E) (M := A)
  obtain ⟨p, hp⟩ : ∃ p : Polynomial E, p = ∏ a ∈ t, minpoly E a := ⟨_, rfl⟩
  refine ⟨p, fun Ω _ _ _ _ φ => ?_⟩
  have hp0 : p ≠ 0 := hp ▸ Finset.prod_ne_zero_iff.2 fun a _ => minpoly.ne_zero (Algebra.IsIntegral.isIntegral a)
  let j : p.SplittingField →ₐ[E] Ω := IsScalarTower.toAlgHom E p.SplittingField Ω
  have hj : Function.Injective j := j.toRingHom.injective
  have hgen : ∀ a ∈ t, φ a ∈ j.range := fun a ha => by
    have h0 : Polynomial.aeval (φ a) p = 0 := by
      rw [Polynomial.aeval_algHom_apply, hp, map_prod, Finset.prod_eq_zero ha (minpoly.aeval E a), map_zero]
    have hs := Polynomial.SplittingField.splits p
    have hr : φ a ∈ ((p.map (algebraMap E p.SplittingField)).map (algebraMap p.SplittingField Ω)).roots := by
      rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq, Polynomial.mem_roots (Polynomial.map_ne_zero hp0),
        Polynomial.IsRoot.def, Polynomial.eval_map_algebraMap]
      exact h0
    rw [hs.roots_map] at hr
    obtain ⟨b, -, hb⟩ := Multiset.mem_map.1 hr
    exact ⟨b, hb⟩
  have hall : ∀ a, φ a ∈ j.range := fun a => by
    have ha : a ∈ Submodule.span E (t : Set A) := ht ▸ trivial
    induction ha using Submodule.span_induction with
    | mem x hx => exact hgen x hx
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact Subalgebra.smul_mem _ hx c
  refine ⟨(AlgEquiv.ofInjective j hj).symm.toAlgHom.comp (φ.codRestrict j.range hall), fun a => ?_⟩
  exact (congrArg Subtype.val ((AlgEquiv.ofInjective j hj).apply_symm_apply ⟨φ a, hall a⟩)).symm

theorem exists_point_factor (E : Type) [Field E] {Z : Scheme.{0}} (f : Z ⟶ Sp E) [IsFinite f] :
    ∃ p : Polynomial E, ∀ (Ω : Type) [Field Ω] [Algebra E Ω] [Algebra p.SplittingField Ω]
      [IsScalarTower E p.SplittingField Ω] (z : Sp Ω ⟶ Z), z ≫ f = spMap (algebraMap E Ω) →
      ∃ z₀ : Sp p.SplittingField ⟶ Z, z₀ ≫ f = spMap (algebraMap E p.SplittingField) ∧
        z = spMap (algebraMap p.SplittingField Ω) ≫ z₀ := by
  have : IsAffine Z := isAffine_of_isAffineHom f
  obtain ⟨g, hg⟩ := Spec.map_surjective (R := CommRingCat.of E) (Z.isoSpec.inv ≫ f)
  have hfin : g.hom.Finite := (IsFinite.SpecMap_iff g).1 (hg ▸ inferInstance)
  let : Algebra E Γ(Z, ⊤) := g.hom.toAlgebra
  have : Module.Finite E Γ(Z, ⊤) := hfin
  obtain ⟨p, hp⟩ := exists_algHom_factor E Γ(Z, ⊤)
  refine ⟨p, fun Ω _ _ _ _ z hz => ?_⟩
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (S := CommRingCat.of Ω) (z ≫ Z.isoSpec.hom)
  have hc : g ≫ ψ = CommRingCat.ofHom (algebraMap E Ω) := Spec.map_injective (by
    rw [Spec.map_comp, hg, hψ, Category.assoc, Iso.hom_inv_id_assoc, hz])
  obtain ⟨φ₀, h₀⟩ := hp Ω { ψ.hom with commutes' := fun a => congrArg (fun q => q.hom a) hc }
  refine ⟨Spec.map (CommRingCat.ofHom φ₀.toRingHom) ≫ Z.isoSpec.inv, ?_, ?_⟩
  · rw [Category.assoc, ← hg, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun a => φ₀.commutes a))
  · rw [← Category.assoc, Iso.eq_comp_inv, ← hψ, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun a => h₀ a))

theorem mem_subPts_iff_of_toBase_eq {F : Type} [Field F] (S : LinSys F) (E E' : Type) [Field E] [Field E'] [Algebra F E]
    [Algebra F E'] [Algebra E E'] {ι : Type} (s : ι → Fin S.N → E)
    {Ω : Type} [Field Ω] [Algebra E Ω] [Algebra E' Ω] [Algebra F Ω] [IsScalarTower F E Ω] [IsScalarTower F E' Ω]
    [IsScalarTower E E' Ω] (x : (S.baseChange E).Pt Ω) (x' : (S.baseChange E').Pt Ω)
    (h : LinSys.toBase x = LinSys.toBase x') :
    x ∈ (S.baseChange E).subPts ((S.baseChange E).cut s) Ω ↔
      x' ∈ (S.baseChange E').subPts ((S.baseChange E').cut fun i k => algebraMap E E' (s i k)) Ω := by
  refine (S.mem_subPts_cut_baseChange_iff E s x).trans
    (Iff.trans ?_ (S.mem_subPts_cut_baseChange_iff E' (fun i k => algebraMap E E' (s i k)) x').symm)
  rw [h]
  simp only [← IsScalarTower.algebraMap_apply]

end GlobalTheory.HSCore.SplitField

namespace GlobalTheory.HSCore


open _root_.GlobalTheory.HSCore.SplitField _root_.GlobalTheory.HSCore.SplitField in
theorem exists_split : ∀ (F : Type) [Field F] [NumberField F] (T : Tuple F) (E : Type) [Field E] [NumberField E] [Algebra F E] (s : Fin T.D → Fin T.N → E), T.IsGoodSection E s → ∃ (E' : Type) (_ : Field E') (_ : NumberField E') (_ : Algebra F E') (_ : Algebra E E') (_ : IsScalarTower F E E'), Split T E' fun i k => algebraMap E E' (s i k) := by
  intro F _ _ T E _ _ _ s hs
  have hfin : IsFinite ((T.linSection E s).subschemeι ≫ (T.toLinSys.baseChange E).str) := hs.finiteEtale.finite
  obtain ⟨p, hp⟩ := exists_point_factor E ((T.linSection E s).subschemeι ≫ (T.toLinSys.baseChange E).str)
  refine ⟨p.SplittingField, inferInstance, NumberField.of_module_finite E _, inferInstance, inferInstance,
    inferInstance, fun x hx => ?_⟩
  let x' : (T.toLinSys.baseChange p.SplittingField).Pt (AlgebraicClosure p.SplittingField) :=
    ⟨x ≫ Scheme.IdealSheafData.subschemeι _, (Category.assoc _ _ _).trans hx⟩
  obtain ⟨y, hy⟩ := (T.toLinSys.toBase_bijective E (AlgebraicClosure p.SplittingField)).2 (LinSys.toBase x')
  obtain ⟨z, hz⟩ := (mem_subPts_iff_of_toBase_eq T.toLinSys E p.SplittingField s y x' hy).2 ⟨x, rfl⟩
  obtain ⟨z₀, h₀, h₁⟩ := hp (AlgebraicClosure p.SplittingField) z (by
    rw [← Category.assoc]; exact (congrArg (· ≫ _) hz).trans y.2)
  let y₀ : (T.toLinSys.baseChange E).Pt p.SplittingField :=
    ⟨z₀ ≫ Scheme.IdealSheafData.subschemeι _, (Category.assoc _ _ _).trans h₀⟩
  obtain ⟨x₁, hx₁⟩ := (T.toLinSys.toBase_bijective p.SplittingField p.SplittingField).2 (LinSys.toBase y₀)
  obtain ⟨x₀, hx₀⟩ := (mem_subPts_iff_of_toBase_eq T.toLinSys E p.SplittingField s y₀ x₁ hx₁.symm).1 ⟨z₀, rfl⟩
  refine ⟨x₀, ?_⟩
  refine (cancel_mono (Scheme.IdealSheafData.subschemeι _)).1 ?_
  refine Eq.trans ?_ ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hx₀)).symm
  refine (T.toLinSys.isPullback_baseChange p.SplittingField).hom_ext ?_ ?_
  · have e₁ : x₁.1 ≫ T.toLinSys.bcFst _ = y₀.1 ≫ T.toLinSys.bcFst _ := congrArg Subtype.val hx₁
    have e₂ : y.1 ≫ T.toLinSys.bcFst _ = x'.1 ≫ T.toLinSys.bcFst _ := congrArg Subtype.val hy
    refine e₂.symm.trans ?_
    rw [Category.assoc, e₁, ← hz, h₁, Category.assoc, Category.assoc]
    rfl
  · refine x'.2.trans ?_
    rw [Category.assoc, x₁.2, ← Spec.map_comp]
    rfl

end GlobalTheory.HSCore
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelExistsAfterBaseChange
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare

namespace GlobalTheory.LevelRaise

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B}

theorem exists_enum (o : Obj D l b s) {M : ℕ} (hM : 0 < M) :
    ∃ (J : Type) (_ : Finite J), ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S),
      ∃ u : J → (Over.mk x ⟶ o.t.G), Function.Injective u ∧ ∀ w, w ^ M = 1 ↔ ∃ j, u j = w := by
  obtain ⟨J, _, π, r, hr, hπ⟩ := LevelFlat.exists_finite_quotient D M hM
  refine ⟨J, inferInstance, fun K _ _ x => ?_⟩
  obtain ⟨β, hβ⟩ := Spec.map_surjective (x ≫ s)
  obtain ⟨-, I, -⟩ := o.geom K x β.hom hβ.symm
  have hI : ∀ a b, I.ev M a = I.ev M b ↔ π a = π b := fun a b => by
    have h : I.ev M a = I.ev M (a - b) * I.ev M b := by rw [← I.add, sub_add_cancel]
    rw [hπ, h, mul_eq_right, I.ker M hM]
    rfl
  refine ⟨fun j => I.ev M (r j), fun i j hij => ?_, fun w => (I.onto M hM w).trans ⟨?_, ?_⟩⟩
  · have := (hI _ _).1 hij
    rwa [hr, hr] at this
  · rintro ⟨a, rfl⟩
    exact ⟨π a, (hI _ _).2 (hr _)⟩
  · rintro ⟨j, rfl⟩
    exact ⟨_, rfl⟩

theorem exists_finite_set (o : Obj D l b s) {M : ℕ} (hM : 0 < M) {K F : Type} [Field K] [Field F] [Algebra K F]
    [IsAlgClosed F] (x : Sp K ⟶ S) :
    ∃ T : Set F, T.Finite ∧ ∀ L : IntermediateField K F, T ⊆ L →
      ∀ w : Over.mk (spMap (algebraMap K F) ≫ x) ⟶ o.t.G, w ^ M = 1 →
        ∃ q : Over.mk (spMap (algebraMap K L) ≫ x) ⟶ o.t.G, spMap (algebraMap L F) ≫ q.left = w.left := by
  haveI := o.proper
  obtain ⟨J, _, hJ⟩ := exists_enum o hM
  obtain ⟨u, -, hu⟩ := hJ F (spMap (algebraMap K F) ≫ x)
  choose T hT using fun j => TorsionRat.exists_finset_over o.t.G x (u j)
  refine ⟨⋃ j, (T j : Set F), Set.finite_iUnion fun j => (T j).finite_toSet, fun L hL w hw => ?_⟩
  obtain ⟨j, rfl⟩ := (hu w).1 hw
  exact hT j L ((Set.subset_iUnion (fun j => (T j : Set F)) j).trans hL)

end GlobalTheory.LevelRaise
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MoveMarkOfIrreducible
section
noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid.MoveMark

section Field

variable {F M : Type} [Field F] [Field M] [Algebra F M]

theorem exists_emb (pb : PowerBasis F M) (τ : F →+* ℂ) (z : ℂ) (hz : (minpoly F pb.gen).eval₂ τ z = 0) :
    ∃ e : M →+* ℂ, (∀ x, e (algebraMap F M x) = τ x) ∧ e pb.gen = z := by
  letI : Algebra F ℂ := τ.toAlgebra
  have h : Polynomial.aeval z (minpoly F pb.gen) = 0 := hz
  exact ⟨(pb.lift z h : M →ₐ[F] ℂ), fun x => (pb.lift z h).commutes x, pb.lift_gen z h⟩

theorem gen_ind (pb : PowerBasis F M) (q : M → Prop) (h0 : q pb.gen) (h1 : ∀ x, q (algebraMap F M x))
    (h2 : ∀ x y, q x → q y → q (x + y)) (h3 : ∀ x y, q x → q y → q (x * y)) (y : M) : q y := by
  have hy : y ∈ Algebra.adjoin F {pb.gen} := by rw [pb.adjoin_gen_eq_top]; trivial
  induction hy using Algebra.adjoin_induction with
  | mem x hx => rw [Set.mem_singleton_iff.1 hx]; exact h0
  | algebraMap r => exact h1 r
  | add x y _ _ hx hy => exact h2 x y hx hy
  | mul x y _ _ hx hy => exact h3 x y hx hy

theorem emb_ext (pb : PowerBasis F M) (e e' : M →+* ℂ) (h1 : ∀ x, e (algebraMap F M x) = e' (algebraMap F M x))
    (h0 : e pb.gen = e' pb.gen) : e = e' :=
  RingHom.ext (gen_ind pb (fun y => e y = e' y) h0 h1 (fun x y hx hy => by simp only [map_add (f := _), hx, hy])
    (fun x y hx hy => by simp only [map_mul, hx, hy]))

theorem emb_root (pb : PowerBasis F M) (e : M →+* ℂ) :
    (minpoly F pb.gen).eval₂ (e.comp (algebraMap F M)) (e pb.gen) = 0 := by
  rw [← Polynomial.hom_eval₂, ← Polynomial.aeval_def, minpoly.aeval, map_zero]

variable [NumberField F] [IsCMField F]

theorem ne_conj (τ : F →+* ℂ) (e e' : M →+* ℂ) (h : ∀ x, e (algebraMap F M x) = τ x)
    (h' : ∀ x, e' (algebraMap F M x) = τ x) : e ≠ ComplexEmbedding.conjugate e' := by
  intro he
  apply IsCMField.complexConj_ne_one F
  ext x
  apply τ.injective
  rw [IsCMField.complexEmbedding_complexConj, ← h' x]
  have := DFunLike.congr_fun he (algebraMap F M x)
  rw [ComplexEmbedding.conjugate_coe_eq] at this
  rw [← this, h]
  rfl

omit [NumberField F] [IsCMField F] in
theorem place_eq (v w : InfinitePlace F) (e e' : M →+* ℂ) (h : ∀ x, e (algebraMap F M x) = w.embedding x)
    (h' : ∀ x, e' (algebraMap F M x) = v.embedding x) (he : e = e' ∨ e = ComplexEmbedding.conjugate e') : w = v := by
  rw [← w.mk_embedding, ← v.mk_embedding]
  rcases he with he | he
  · congr 1
    ext x
    rw [← h, ← h', he]
  · rw [← InfinitePlace.mk_conjugate_eq v.embedding]
    congr 1
    ext x
    rw [← h, he, ComplexEmbedding.conjugate_coe_eq, ComplexEmbedding.conjugate_coe_eq, h']

end Field

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p}

theorem sh_mul (x y : G.C) : sh G (x * y) = sh G y * sh G x := by
  simp only [sh, map_mul, MulOpposite.unop_mul]

theorem sh_add (x y : G.C) : sh G (x + y) = sh G x + sh G y := by
  simp only [sh, map_add (f := _), MulOpposite.unop_add]

variable {M : Type} [Field M] [NumberField M] [Algebra G.F M]

theorem conj_law (P : Pair G) (pb : PowerBasis G.F M) (j : M →ₐ[G.F] G.C) (hj : j pb.gen = P.γ) (σ : M →+* M)
    (hσ : ∀ x : G.F, σ (algebraMap G.F M x) = algebraMap G.F M (IsCMField.complexConj G.F x))
    (hπ : σ pb.gen * pb.gen = ((P.c : ℚ) : M)) (y : M) : (P.β : G.C) * sh G (j y) = j (σ y) * P.β := by
  refine gen_ind pb (fun y => (P.β : G.C) * sh G (j y) = j (σ y) * P.β) ?_ ?_ ?_ ?_ y
  · have h1 : (P.γ : G.C) * j (σ pb.gen) = algebraMap ℚ G.C P.c := by
      rw [← hj, ← map_mul, mul_comm, hπ, IsScalarTower.algebraMap_apply ℚ G.F G.C, ← j.commutes]
      congr 1
      simp
    show (P.β : G.C) * sh G (j pb.gen) = j (σ pb.gen) * P.β
    apply P.γ.isUnit.mul_left_cancel
    rw [hj, ← mul_assoc, P.sim, ← mul_assoc, h1]
  · intro x
    show (P.β : G.C) * sh G (j (algebraMap G.F M x)) = j (σ (algebraMap G.F M x)) * P.β
    rw [hσ, j.commutes, j.commutes, sh, G.star_F, Algebra.commutes]
  · intro x y hx hy
    show (P.β : G.C) * sh G (j (x + y)) = j (σ (x + y)) * P.β
    rw [map_add (f := _), sh_add, mul_add, hx, hy, map_add (f := _), map_add (f := _), add_mul]
  · intro x y hx hy
    show (P.β : G.C) * sh G (j (x * y)) = j (σ (x * y)) * P.β
    rw [map_mul, sh_mul, ← mul_assoc, hy, mul_assoc, hx, ← mul_assoc, ← map_mul, ← map_mul, mul_comm y x]

omit [NumberField M] in
theorem comm_law (γ : G.C) (pb : PowerBasis G.F M) (j : M →ₐ[G.F] G.C) (hj : j pb.gen = γ) (y : G.C)
    (hy : y * γ = γ * y) (m : M) : y * j m = j m * y := by
  refine gen_ind pb (fun m => y * j m = j m * y) ?_ ?_ ?_ ?_ m
  · show y * j pb.gen = j pb.gen * y
    rw [hj, hy]
  · intro x
    show y * j (algebraMap G.F M x) = j (algebraMap G.F M x) * y
    rw [j.commutes, Algebra.commutes]
  · intro a b ha hb
    show y * j (a + b) = j (a + b) * y
    rw [map_add (f := _), mul_add, add_mul, ha, hb]
  · intro a b ha hb
    show y * j (a * b) = j (a * b) * y
    rw [map_mul, ← mul_assoc, ha, mul_assoc, hb, mul_assoc]

theorem triv_mul_inv (R : Type) [CommRing R] [Algebra ℚ R] (β β' : G.C) (x U : (R ⊗[ℚ] G.C)ˣ) (t : Rˣ)
    (hU : (U : R ⊗[ℚ] G.C) * inC G R β * (starT G.star R U).unop = inC G R β') (hx : Triv G R β x t) :
    Triv G R β' (x * U⁻¹) t := by
  unfold Triv at hx ⊢
  have h1 : (starT G.star R U).unop * (starT G.star R ((U⁻¹ : (R ⊗[ℚ] G.C)ˣ) : R ⊗[ℚ] G.C)).unop = 1 := by
    rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
  rw [← hx, ← hU, Units.val_mul, map_mul, MulOpposite.unop_mul]
  calc _ = (x : R ⊗[ℚ] G.C) * (((U⁻¹ : (R ⊗[ℚ] G.C)ˣ) : R ⊗[ℚ] G.C) * U) * inC G R β *
        ((starT G.star R U).unop * (starT G.star R ((U⁻¹ : (R ⊗[ℚ] G.C)ˣ) : R ⊗[ℚ] G.C)).unop) *
        (starT G.star R x).unop := by simp only [mul_assoc]
    _ = _ := by rw [h1, Units.inv_mul, mul_one, mul_one]


omit [NumberField M] in
theorem exists_basis (ha : G.a = 1) (P : Pair G) (μ : ℂ) (hm : P.Mark μ) (pb : PowerBasis G.F M)
    (hpol : P.pol = minpoly G.F pb.gen) (j : M →ₐ[G.F] G.C) (hj : j pb.gen = P.γ) (w : InfinitePlace G.F) :
    ∃ (Z : GL (Fin G.n) ℂ) (d : Fin G.n → ℝ) (e : Fin G.n → (M →+* ℂ)),
      (∀ i x, e i (algebraMap G.F M x) = w.embedding x) ∧ Function.Injective (fun i => e i pb.gen) ∧
      (∀ z : ℂ, P.pol.eval₂ w.embedding z = 0 → ∃ i, e i pb.gen = z) ∧
      (∀ y, G.psi w (j y) * (Z : Matrix (Fin G.n) (Fin G.n) ℂ) =
        (Z : Matrix (Fin G.n) (Fin G.n) ℂ) * Matrix.diagonal (fun i => e i y)) ∧ (∀ i, d i ≠ 0) ∧
      (Z : Matrix (Fin G.n) (Fin G.n) ℂ)ᴴ * (G.gram w * G.psi w ((P.β⁻¹ : G.Cˣ) : G.C)) *
        (Z : Matrix (Fin G.n) (Fin G.n) ℂ) = Matrix.diagonal (fun i => (d i : ℂ)) := by
  obtain ⟨Z, lam, hinj, hroot, hZ⟩ := GlobalTheory.T.exists_eigenbasis_psi_infinitePlace_distinct_roots p G P w
  have hr : ∀ i, P.pol.eval₂ w.embedding (lam i) = 0 := fun i => (hroot _).2 ⟨i, rfl⟩
  choose e he he' using fun i => exists_emb pb w.embedding (lam i) (hpol ▸ hr i)
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.similitudePair_hermitianForm_invertible_similitude p G P w
  obtain ⟨d, hd, hD⟩ := GlobalTheory.T.exists_diagonal_congr_of_similitude_distinct_eigenvalues _ (G.psi w P.γ) ((P.c : ℚ) : ℝ) Z lam h1 h2
    (by exact_mod_cast P.c.ne_zero) (by rw [h3]; simp) hinj
    (fun i => GlobalTheory.T.marked_similitude_pair_minpoly_roots_normSq_eq p G P μ ha hm _ _ (hr i)) hZ
  have hl : (fun i => e i pb.gen) = lam := funext he'
  refine ⟨Z, d, e, he, hl ▸ hinj, fun z hz => ?_, fun y => ?_, hd, hD⟩
  · obtain ⟨i, hi⟩ := (hroot z).1 hz
    exact ⟨i, (he' i).trans hi⟩
  · refine gen_ind pb (fun y => G.psi w (j y) * (Z : Matrix (Fin G.n) (Fin G.n) ℂ) =
        (Z : Matrix (Fin G.n) (Fin G.n) ℂ) * Matrix.diagonal (fun i => e i y)) ?_ ?_ ?_ ?_ y
    · show G.psi w (j pb.gen) * _ = _
      rw [hj, hl, hZ]
    · intro x
      show G.psi w (j (algebraMap G.F M x)) * _ = _
      simp only [he]
      rw [j.commutes, G.psi_F]
      exact (Matrix.scalar_commute _ (fun _ => Commute.all _ _) _).eq
    · intro a b h h'
      show G.psi w (j (a + b)) * _ = _
      simp only [map_add (f := _)]
      rw [Matrix.add_mul, h, h', ← Matrix.mul_add, Matrix.diagonal_add]
    · intro a b h h'
      show G.psi w (j (a * b)) * _ = _
      simp only [map_mul]
      rw [Matrix.mul_assoc, h', ← Matrix.mul_assoc, h, Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]

end GlobalTheory.LKMid.MoveMark

namespace GlobalTheory.LKMid

end GlobalTheory.LKMid
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulPowMemAndSpaceVLe
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

namespace GlobalTheory.HSCore

variable {K : Type} [Field K] [NumberField K]

theorem monoDeg_succ_split {ι : Type} [Fintype ι] {a : ℕ} (β : MonoDeg ι (a + 1)) :
    ∃ (i : ι) (α : MonoDeg ι a), β.1 = α.1 + Finsupp.single i 1 := by
  have hne : β.1 ≠ 0 := fun h0 => by
    have := β.2
    rw [h0, Finsupp.degree_eq_sum] at this
    simp at this
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 hne
  have hle : Finsupp.single i 1 ≤ β.1 := by
    rw [Finsupp.single_le_iff]
    simp only [Finsupp.coe_zero, Pi.zero_apply] at hi
    omega
  have e : β.1 = (β.1 - Finsupp.single i 1) + Finsupp.single i 1 := (tsub_add_cancel_of_le hle).symm
  refine ⟨i, ⟨β.1 - Finsupp.single i 1, ?_⟩, e⟩
  have h2 := β.2
  rw [e, Finsupp.degree_eq_sum, Finset.sum_congr rfl (fun x _ => Finsupp.add_apply _ _ x),
    Finset.sum_add_distrib, ← Finsupp.degree_eq_sum, ← Finsupp.degree_eq_sum, Finsupp.degree_single] at h2
  omega

theorem mulPow_mem (X : Data K) (s : Fin X.D → Fin X.N → K) (hX : X.MulStable) :
    ∀ (a j l : ℕ) (h : j + a = l), l ≤ X.T → ∀ (α : MonoDeg (Fin X.D) a), ∀ m ∈ X.V j,
      mulPow X.toGeo s h α m ∈ X.V l := by
  intro a
  induction a with
  | zero =>
    intro j l h _ α m hm
    subst h
    have : mulPow X.toGeo s (rfl : j + 0 = j + 0) α m = m := by
      unfold mulPow
      exact mulMono_zero _ _ _ _ _ _
    rw [this]
    exact hm
  | succ a ih =>
    intro j l h hl β m hm
    subst h
    obtain ⟨i, α, e⟩ := monoDeg_succ_split β
    have hk : j + a < X.T := by omega
    have key : mulPow X.toGeo s (rfl : j + (a + 1) = j + (a + 1)) β m =
        X.mulW (j + a) (s i) (mulPow X.toGeo s (rfl : j + a = j + a) α m) := by
      unfold mulPow
      rw [Geo.mulW_apply]
      exact mulMono_succ _ _ _ α β i e _ _ _ m
    rw [key]
    exact hX.mem hk (s i) ⟨_, ih j (j + a) rfl (by omega) α m hm⟩

theorem mulPow_mem_and_spaceV_le : ∀ (K : Type) [Field K] [NumberField K] (X : Data K) (s : Fin X.D → Fin X.N → K),
    X.MulStable → (∀ (a j l : ℕ) (h : j + a = l), l ≤ X.T → ∀ (α : MonoDeg (Fin X.D) a), ∀ m ∈ X.V j,
      mulPow X.toGeo s h α m ∈ X.V l) ∧ spaceV X s ≤ X.V X.T := by
  intro K _ _ X s hX
  refine ⟨mulPow_mem X s hX, ?_⟩
  refine sup_le (X.global_le X.T le_rfl) (iSup_le fun α => ?_)
  rintro _ ⟨m, hm, rfl⟩
  exact mulPow_mem X s hX _ _ _ _ le_rfl α m hm

end GlobalTheory.HSCore
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormLeOneOfSumSqLtOne
section
namespace GlobalTheory.NormBoundSumSquares

theorem norm_le_one_of_sum_sq_lt_one :
    (let d1 : {E : Type} → [inst : Field E] → [NumberField E] → {a : ℕ} → GlobalTheory.CuspRep.Lie E a → ℝ := @(fun {E : Type} [Field E] [NumberField E] {a : ℕ} (x : GlobalTheory.CuspRep.Lie E a) ↦ ∑ w : NumberField.InfinitePlace E, ∑ i : Fin a, ∑ j : Fin a, ‖x i j w‖ ^ (2 : ℕ)); ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [NumberField.IsTotallyComplex E] {a : ℕ} (x : GlobalTheory.CuspRep.Lie E a), d1 x < (1 : ℝ) → ‖x‖ ≤ (1 : ℝ)) := by
  intro d1 E _ _ _ a x hx
  have hsum : ∑ w : NumberField.InfinitePlace E, ∑ i : Fin a, ∑ j : Fin a, ‖x i j w‖ ^ (2 : ℕ) < 1 := hx
  have entry : ∀ (i j : Fin a) (w : NumberField.InfinitePlace E), ‖x i j w‖ ≤ 1 := by
    intro i j w
    by_contra hcon
    have hgt : 1 < ‖x i j w‖ := lt_of_not_ge hcon
    have hsq : 1 < ‖x i j w‖ ^ (2 : ℕ) := one_lt_pow₀ hgt (by norm_num)
    have h₃ : ‖x i j w‖ ^ (2 : ℕ) ≤ ∑ j' : Fin a, ‖x i j' w‖ ^ (2 : ℕ) :=
      Finset.single_le_sum (f := fun j' => ‖x i j' w‖ ^ (2 : ℕ))
        (fun _ _ => by positivity) (Finset.mem_univ j)
    have h₂ : ∑ j' : Fin a, ‖x i j' w‖ ^ (2 : ℕ)
        ≤ ∑ i' : Fin a, ∑ j' : Fin a, ‖x i' j' w‖ ^ (2 : ℕ) :=
      Finset.single_le_sum (f := fun i' => ∑ j' : Fin a, ‖x i' j' w‖ ^ (2 : ℕ))
        (fun _ _ => by positivity) (Finset.mem_univ i)
    have h₁ : ∑ i' : Fin a, ∑ j' : Fin a, ‖x i' j' w‖ ^ (2 : ℕ)
        ≤ ∑ w' : NumberField.InfinitePlace E, ∑ i' : Fin a, ∑ j' : Fin a, ‖x i' j' w'‖ ^ (2 : ℕ) :=
      Finset.single_le_sum (f := fun w' => ∑ i' : Fin a, ∑ j' : Fin a, ‖x i' j' w'‖ ^ (2 : ℕ))
        (fun _ _ => by positivity) (Finset.mem_univ w)
    linarith
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
  exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun w => entry i j w

end GlobalTheory.NormBoundSumSquares
end

