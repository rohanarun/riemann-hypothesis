module

public import Mathlib
public import Formalism.LocalToGlobal.Columns.ToHLatLemmas
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0012
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0048
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0052
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0731
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamFramedOfPos
section
namespace GlobalTheory.FamilyFrames

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

theorem posDef_sum_dep {ι γ : Type} {κ : γ → Type} [Fintype ι] [Fintype γ] [∀ c, Fintype (κ c)]
    (G : ∀ c, Matrix (κ c) (κ c) ℂ) (hG : ∀ c, (G c).PosDef) (P : ∀ c, Matrix (κ c) ι ℂ)
    (hinj : ∀ x, (∀ c, P c *ᵥ x = 0) → x = 0) : (∑ c, (P c)ᴴ * G c * P c).PosDef := by
  have hs : ∀ c, ((P c)ᴴ * G c * P c).PosSemidef := fun c =>
    (hG c).posSemidef.conjTranspose_mul_mul_same (P c)
  have hS := Matrix.posSemidef_sum (s := Finset.univ) (fun c _ => hs c)
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hS.1 fun x hx => ?_
  rw [Matrix.sum_mulVec, dotProduct_sum]
  obtain ⟨c, hc⟩ : ∃ c, P c *ᵥ x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hx (hinj x hcon)
  refine Finset.sum_pos' (fun c _ => (hs c).dotProduct_mulVec_nonneg x) ⟨c, Finset.mem_univ c, ?_⟩
  have h1 := (hG c).dotProduct_mulVec_pos hc
  have h2 : star x ⬝ᵥ (((P c)ᴴ * G c * P c) *ᵥ x) = star (P c *ᵥ x) ⬝ᵥ (G c *ᵥ (P c *ᵥ x)) := by
    simp only [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
  rw [h2]
  exact h1

section Generic

open Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HermitianLatticesTheory

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem isSesq_pi {γ : Type} [Fintype γ] {V : γ → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module K (V c)]
    (H : ∀ c, InfinitePlace K → V c → V c → ℂ) (hH : ∀ c, IsSesq (H c)) :
    IsSesq (fun v (x y : ∀ c, V c) => ∑ c, H c v (x c) (y c)) := by
  intro v
  refine ⟨fun x x' y => ?_, fun x y y' => ?_, fun a x y => ?_, fun a x y => ?_⟩
  · simp only [Pi.add_apply, fun c => (hH c v).1, Finset.sum_add_distrib]
  · simp only [Pi.add_apply, fun c => (hH c v).2.1, Finset.sum_add_distrib]
  · simp only [Pi.smul_apply, fun c => (hH c v).2.2.1, Finset.mul_sum]
  · simp only [Pi.smul_apply, fun c => (hH c v).2.2.2, Finset.mul_sum]

theorem posAt_pi {γ : Type} [Fintype γ] [DecidableEq γ] {V : γ → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module K (V c)]
    {κ : γ → Type} [∀ c, Fintype (κ c)] [∀ c, DecidableEq (κ c)] (b : ∀ c, Basis (κ c) K (V c))
    (H : ∀ c, InfinitePlace K → V c → V c → ℂ) (hH : ∀ c, IsSesq (H c)) (hP : ∀ c, PosAt (b c) (H c)) :
    PosAt (Pi.basis b) (fun v (x y : ∀ c, V c) => ∑ c, H c v (x c) (y c)) := by
  intro v
  let P : ∀ c, Matrix (κ c) (Σ c, κ c) ℂ := fun c => Matrix.of fun i s => vecAt (b c) v (Pi.basis b s c) i
  have hgram : gramOf (Pi.basis b) (fun (x y : ∀ c, V c) => ∑ c, H c v (x c) (y c)) =
      ∑ c, (P c)ᴴ * gramOf (b c) (H c v) * P c := by
    ext s t
    simp only [Matrix.sum_apply]
    rw [gramOf, Matrix.of_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [sesq_eq_sum (hH c) (b c) v]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul, P, Matrix.of_apply]
    rw [Finset.sum_comm]
    rfl
  rw [hgram]
  refine posDef_sum_dep _ (fun c => hP c v) P fun x hx => ?_
  funext ⟨c, i⟩
  have h1 := congrFun (hx c) i
  have h2 : ∀ s, P c i s = if s = ⟨c, i⟩ then 1 else 0 := by
    intro s
    have : P c i s = v.embedding ((Pi.basis b).repr (Pi.basis b s) ⟨c, i⟩) := by
      rw [Pi.basis_repr]
      rfl
    rw [this, Basis.repr_self, Finsupp.single_apply]
    split_ifs <;> simp
  simpa [Matrix.mulVec, dotProduct, h2] using h1

theorem exists_frames {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι] (b : Basis ι K V)
    (H : InfinitePlace K → V → V → ℂ) (hH : IsSesq H) (hP : PosAt b H) :
    ∃ (n : ℕ) (e : (Fin n → K) ≃ₗ[K] V) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ), (∀ v, IsUnit (X v).det) ∧
      ∀ v x, ((normAt (Pi.basisFun K (Fin n)) X v x ^ 2 : ℝ) : ℂ) = H v (e x) (e x) := by
  let e : (Fin (Fintype.card ι) → K) ≃ₗ[K] V := (b.reindex (Fintype.equivFin ι)).equivFun.symm
  let c := Pi.basisFun K (Fin (Fintype.card ι))
  have hH' := isSesq_comp hH e.toLinearMap
  have hP' := posAt_comp b c hH hP e.toLinearMap e.injective
  have hs := fun v => frameOf_spec (hP' v)
  refine ⟨_, e, fun v => frameOf (gramOf c fun x y => H v (e x) (e y)), fun v => (hs v).1, fun v x => ?_⟩
  rw [← majAt_self]
  have e1 := sesq_eq_sum (isSesq_maj c (fun v => frameOf (gramOf c fun x y => H v (e x) (e y)))) c v x x
  have e2 := sesq_eq_sum hH' c v x x
  rw [gramOf_maj] at e1
  refine e1.trans (Eq.trans ?_ e2.symm)
  have e3 := (hs v).2
  simp only [LinearEquiv.coe_coe] at e3 ⊢
  rw [e3]

theorem famFramed_of_pos (F : Formalism.L2.Col.GFam K) (h : F.Ok)
    (hpos : ∀ b (v : InfinitePlace K), ((F.mem b).gramV.map v.embedding).PosDef) : GlobalTheory.ColRows.FamFramed F h :=
  exists_frames (Pi.basis fun b => (F.mem b).hB (h b)) _
    (isSesq_pi (fun b v (φ ψ : (F.mem b).EqFun) => (F.mem b).ipAt (h b) v φ ψ) fun b => (F.mem b).isSesq_ipAt (h b))
    (posAt_pi _ (fun b v (φ ψ : (F.mem b).EqFun) => (F.mem b).ipAt (h b) v φ ψ) (fun b => (F.mem b).isSesq_ipAt (h b))
      fun b => (F.mem b).posAt_ipAt (h b) (hpos b) _)

end Generic

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef _root_.Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows

theorem famFramed_chF : ∀ (X : Fields) (hX : X.Ok) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (I : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (u : Pr.Word) (j : ℕ) (h : (chF W sel mu I u j).Ok), FamFramed (chF W sel mu I u j) h := by
  intro X hX Pr R W _ sel Sg mu I u j h
  exact famFramed_of_pos _ h fun _ v =>
    (roundPk_ratP (W.lamTrue u j) (fun d : DecoSet (E := X.E) (n := R.N j) (ST := Pr.vT u) (SG := Pr.vGs) => d.1.Lsh) hX).pos v

end GlobalTheory.FamilyFrames
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankEqTwoMul
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows

namespace GlobalTheory.PlaceWeights


open Classical in
theorem sum_ind_algHom (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (v : InfinitePlace K) :
    (∑ f : K →ₐ[ℚ] ℂ, (if InfinitePlace.mk (f : K →+* ℂ) = v then (1 : ℝ) else 0)) = 2 := by
  have h1 : (∑ f : K →ₐ[ℚ] ℂ, (if InfinitePlace.mk (f : K →+* ℂ) = v then (1 : ℝ) else 0))
      = ∑ f : K →+* ℂ, (if InfinitePlace.mk f = v then (1 : ℝ) else 0) :=
    (Fintype.sum_equiv (RingHom.equivRatAlgHom (R := K) (S := ℂ)) _ _ (fun _ => rfl)).symm
  rw [h1, Finset.sum_boole, InfinitePlace.card_filter_mk_eq, IsTotallyComplex.mult_eq]
  norm_num

theorem finrank_eq_two_mul (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] :
    Module.finrank ℚ K = 2 * Fintype.card (InfinitePlace K) := by
  rw [← InfinitePlace.sum_mult_eq]
  simp [IsTotallyComplex.mult_eq, mul_comm]


open Classical in
theorem sum_ind_placeUnder (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (σ₀ : K →+* ℂ)
    (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] (h : ∀ k, σ₀ k ∈ M) (v : InfinitePlace K) :
    (∑ ρ : M →ₐ[ℚ] ℂ, (if placeUnder σ₀ h ρ = v then (1 : ℝ) else 0)) / (Module.finrank ℚ M : ℝ)
      = 1 / (Fintype.card (InfinitePlace K) : ℝ) := by
  let _ : Algebra K M := (σ₀.codRestrict M h).toAlgebra
  have : IsScalarTower ℚ K M := IsScalarTower.of_algebraMap_eq (fun x => by simp)
  have key := (GlobalTheory.EmbeddingMean.tower (K := ℚ) (A := K) (B := M) (C := ℂ)).2
    (fun f => if InfinitePlace.mk (f : K →+* ℂ) = v then (1 : ℝ) else 0)
  rw [sum_ind_algHom, finrank_eq_two_mul K] at key
  have hc : (Fintype.card (InfinitePlace K) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  refine Eq.trans ?_ (key.trans ?_)
  · rfl
  · push_cast
    field_simp

theorem exists_weights : ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (σ₀ : K →+* ℂ) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] (h : ∀ k, σ₀ k ∈ M), ∃ wt : InfinitePlace K → (M →ₐ[ℚ] ℂ) → ℝ, (∀ v ρ, 0 ≤ wt v ρ) ∧ (∀ v, ∑ ρ, wt v ρ = 1) ∧ (∀ v ρ, wt v ρ ≠ 0 → placeUnder σ₀ h ρ = v) ∧ ∀ ρ, (∑ v, wt v ρ) / (Fintype.card (InfinitePlace K) : ℝ) = 1 / (Module.finrank ℚ M : ℝ) := by
  classical
  intro K _ _ _ σ₀ M _ h
  have hc : (Fintype.card (InfinitePlace K) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hM : (Module.finrank ℚ M : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := M)).ne'
  refine ⟨fun v ρ => (if placeUnder σ₀ h ρ = v then (1 : ℝ) else 0) *
    ((Fintype.card (InfinitePlace K) : ℝ) / (Module.finrank ℚ M : ℝ)), ?_, ?_, ?_, ?_⟩
  · intro v ρ
    refine mul_nonneg ?_ (by positivity)
    split_ifs <;> norm_num
  · intro v
    have key := sum_ind_placeUnder K σ₀ M h v
    rw [← Finset.sum_mul]
    rw [div_eq_div_iff hM hc] at key
    rw [← mul_div_assoc, div_eq_one_iff_eq hM]
    convert key using 1
    ring
  · intro v ρ hw
    by_contra hne
    exact hw (by simp [hne])
  · intro ρ
    rw [← Finset.sum_mul, Finset.sum_ite_eq]
    simp only [Finset.mem_univ, if_true]
    field_simp

end GlobalTheory.PlaceWeights
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankRangeBaseChangeEqFinrankRangeDualMap
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem finrank_range_baseChange_eq_dualMap_and_finrank_dual :
    ∀ (O : Type) [CommRing O] (K : Type) [Field K] [Algebra O K] (M₁ : Type) [AddCommGroup M₁] [Module O M₁] [Module.Free O M₁] [Module.Finite O M₁] (M₂ : Type) [AddCommGroup M₂] [Module O M₂] [Module.Free O M₂] [Module.Finite O M₂] (f : M₁ →ₗ[O] M₂), Module.finrank K (LinearMap.range (f.baseChange K)) = Module.finrank K (LinearMap.range (f.dualMap.baseChange K)) ∧ Module.finrank K (K ⊗[O] M₁) = Module.finrank K (K ⊗[O] Module.Dual O M₁) := by
  intro O _ K _ _ M₁ _ _ _ _ M₂ _ _ _ _ f
  obtain ⟨h1, h2⟩ := GlobalTheory.DualFibreRank.finrank_dual_and_range_dualMap_baseChange O M₁ M₂ K f
  exact ⟨h2.symm, h1.symm⟩

end GlobalTheory.AbCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueWit
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.EndLoc.HomGlue

theorem pmap_hom_ext {S Z Y : Scheme.{0}} (A : Over S) (𝒰 : Z.OpenCover) (t : Z ⟶ S)
    {g₁ g₂ : pullback A.hom t ⟶ Y} (h : ∀ i, pmap A t (𝒰.f i) ≫ g₁ = pmap A t (𝒰.f i) ≫ g₂) : g₁ = g₂ := by
  refine Scheme.Cover.hom_ext (𝒰.pullback₁ (pullback.snd A.hom t)) _ _ fun (i : 𝒰.I₀) => ?_
  have w : (pullback.fst (pullback.snd A.hom t) (𝒰.f i) ≫ pullback.fst A.hom t) ≫ A.hom =
      pullback.snd (pullback.snd A.hom t) (𝒰.f i) ≫ 𝒰.f i ≫ t := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc]
  have e : pullback.fst (pullback.snd A.hom t) (𝒰.f i) = pullback.lift _ _ w ≫ pmap A t (𝒰.f i) := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, pullback.condition]
  show pullback.fst (pullback.snd A.hom t) (𝒰.f i) ≫ g₁ = pullback.fst (pullback.snd A.hom t) (𝒰.f i) ≫ g₂
  rw [e, Category.assoc, Category.assoc, h]

theorem over_hom_ext_cover {Z : Scheme.{0}} (𝒰 : Z.OpenCover) {X Y : Over Z} {g₁ g₂ : X ⟶ Y}
    (h : ∀ i, (Over.pullback (𝒰.f i)).map g₁ = (Over.pullback (𝒰.f i)).map g₂) : g₁ = g₂ := by
  apply Over.OverMorphism.ext
  refine Scheme.Cover.hom_ext (𝒰.pullback₁ X.hom) _ _ fun (i : 𝒰.I₀) => ?_
  have e1 : ((Over.pullback (𝒰.f i)).map g₁).left ≫ pullback.fst Y.hom (𝒰.f i) =
      pullback.fst X.hom (𝒰.f i) ≫ g₁.left := pullback.lift_fst _ _ _
  have e2 : ((Over.pullback (𝒰.f i)).map g₂).left ≫ pullback.fst Y.hom (𝒰.f i) =
      pullback.fst X.hom (𝒰.f i) ≫ g₂.left := pullback.lift_fst _ _ _
  show pullback.fst X.hom (𝒰.f i) ≫ g₁.left = pullback.fst X.hom (𝒰.f i) ≫ g₂.left
  rw [← e1, ← e2, h i]

theorem isMonHom_of_cover {Z : Scheme.{0}} (𝒰 : Z.OpenCover) {G H : Over Z} [MonObj G] [MonObj H] (f : G ⟶ H)
    (hf : ∀ i, IsMonHom ((Over.pullback (𝒰.f i)).map f)) : IsMonHom f := by
  constructor
  · refine over_hom_ext_cover 𝒰 fun i => ?_
    have h := (hf i).one_hom
    rw [Functor.obj.η_def, Functor.obj.η_def, Category.assoc, cancel_epi] at h
    rw [Functor.map_comp, h]
  · refine over_hom_ext_cover 𝒰 fun i => ?_
    have h := (hf i).mul_hom
    rw [Functor.obj.μ_def, Functor.obj.μ_def, Functor.LaxMonoidal.μ_natural_assoc, Category.assoc,
      cancel_epi] at h
    rw [Functor.map_comp, Functor.map_comp, h]

theorem lbIso_pull_pull {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) (a : Y ⟶ X) (b : Y' ⟶ Y) :
    LBIso ((L.pull a).pull b) (L.pull (b ≫ a)) :=
  LBIso.chartPull (chartPullLinComb L a (fun _ : PUnit => b) (fun _ => b ≫ a) (fun _ => 1) (𝟙 _)
    fun _ => (Category.id_comp _).symm) (chartPullId _) (GlobalTheory.PolBaseChange.lbIso_refl (LB.isLB_pull hL _))

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] {L : LB A.left} {M : LB B.left}

theorem wit_w {Z Z' : Scheme.{0}} {t : Z ⟶ S} {f : pullback A.hom t ⟶ B.left} (g : Z' ⟶ Z)
    (h : Wit A B L M (g ≫ t) (pmap A t g ≫ f)) :
    pmap A t g ≫ f ≫ B.hom = pmap A t g ≫ pullback.snd A.hom t ≫ t := by
  obtain ⟨A', B', _, _, φA, φB, Φ, hA, hB, -, -, e, e1, e2, e3⟩ := h
  haveI : IsIso e := by
    have : e = hA.1.isoPullback.hom :=
      pullback.hom_ext (by rw [e1, IsPullback.isoPullback_hom_fst]) (by rw [e2, IsPullback.isoPullback_hom_snd])
    rw [this]
    infer_instance
  rw [← cancel_epi e]
  calc e ≫ pmap A t g ≫ f ≫ B.hom = (e ≫ pmap A t g ≫ f) ≫ B.hom := by simp only [Category.assoc]
    _ = A'.hom ≫ g ≫ t := by rw [e3, Category.assoc, hB.1.w, Over.w_assoc]
    _ = e ≫ pmap A t g ≫ pullback.snd A.hom t ≫ t := by
        rw [pullback.lift_snd_assoc, Category.assoc, reassoc_of% e2]

theorem isMonHom_pull_of_wit {Z Z' : Scheme.{0}} {t : Z ⟶ S} {f : pullback A.hom t ⟶ B.left} (g : Z' ⟶ Z)
    (h : Wit A B L M (g ≫ t) (pmap A t g ≫ f)) (Φ : (Over.pullback t).obj A ⟶ (Over.pullback t).obj B)
    (hΦ : Φ.left ≫ pullback.fst B.hom t = f) : IsMonHom ((Over.pullback g).map Φ) := by
  obtain ⟨A', B', _, _, φA, φB, Φ', hA, hB, hΦ', -, e, e1, e2, e3⟩ := h
  have hPA := (isGrpPullback_pullback ((Over.pullback t).obj A) g).comp (isGrpPullback_pullback A t)
  have hPB := (isGrpPullback_pullback ((Over.pullback t).obj B) g).comp (isGrpPullback_pullback B t)
  obtain ⟨a, ha, ha'⟩ := grpPullback_iso hPA hA
  obtain ⟨b, hb, hb'⟩ := grpPullback_iso hB hPB
  have key : a.hom.left ≫ e ≫ pmap A t g = pullback.fst _ g := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, pullback.lift_fst, e1, ha']
    · rw [Category.assoc, Category.assoc, pullback.lift_snd, reassoc_of% e2, Over.w_assoc a.hom]
      exact pullback.condition.symm
  have hmap : ((Over.pullback g).map Φ).left ≫ pullback.fst _ g = pullback.fst _ g ≫ Φ.left :=
    pullback.lift_fst _ _ _
  have eq : (Over.pullback g).map Φ = a.hom ≫ Φ' ≫ b.hom := by
    apply Over.OverMorphism.ext
    apply hPB.1.hom_ext
    · have lhs : ((Over.pullback g).map Φ).left ≫ pullback.fst _ g ≫ pullback.fst B.hom t =
          pullback.fst _ g ≫ f := by
        rw [← Category.assoc, hmap, Category.assoc, hΦ]
      have rhs : (a.hom ≫ Φ' ≫ b.hom).left ≫ pullback.fst _ g ≫ pullback.fst B.hom t =
          pullback.fst _ g ≫ f := by
        simp only [Over.comp_left, Category.assoc]
        rw [hb', ← e3, ← key]
        simp only [Category.assoc]
      exact lhs.trans rhs.symm
    · exact (Over.w _).trans (Over.w _).symm
  rw [eq]
  infer_instance

theorem local_iso (hL : L.IsLB) (hM : M.IsLB) {Z Z' : Scheme.{0}} {t : Z ⟶ S} {f : pullback A.hom t ⟶ B.left}
    (g : Z' ⟶ Z) [IsOpenImmersion g] (h : Wit A B L M (g ≫ t) (pmap A t g ≫ f))
    (Φ : (Over.pullback t).obj A ⟶ (Over.pullback t).obj B) (hΦ : Φ.left ≫ pullback.fst B.hom t = f) :
    LBIso ((L.pull (pullback.fst A.hom t)).pull (((Over.pullback t).obj A).hom ⁻¹ᵁ g.opensRange).ι)
      (((M.pull (pullback.fst B.hom t)).pull Φ.left).pull
        (((Over.pullback t).obj A).hom ⁻¹ᵁ g.opensRange).ι) := by
  obtain ⟨A', B', _, _, φA, φB, Φ', hA, hB, -, hI, e, e1, e2, e3⟩ := h
  set U := ((Over.pullback t).obj A).hom ⁻¹ᵁ g.opensRange with hU
  have hr : Set.range ⇑(U.ι ≫ pullback.snd A.hom t) ⊆ Set.range ⇑g := by
    rintro _ ⟨x, rfl⟩
    have hx : U.ι x ∈ (U : Set _) := Scheme.Opens.range_ι U ▸ ⟨x, rfl⟩
    exact Scheme.Hom.mem_opensRange.1 hx
  have hl : IsOpenImmersion.lift g _ hr ≫ g = U.ι ≫ pullback.snd A.hom t := IsOpenImmersion.lift_fac _ _ _
  have wl : (U.ι ≫ pullback.fst A.hom t) ≫ A.hom = IsOpenImmersion.lift g _ hr ≫ g ≫ t := by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact (congrArg (· ≫ t) hl.symm).trans (Category.assoc _ _ _)
  have he' : pullback.lift _ _ wl ≫ pmap A t g = U.ι := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, hl]
  have he : hA.1.isoPullback.inv ≫ e = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, e1, IsPullback.isoPullback_inv_fst, Category.id_comp]
    · rw [Category.assoc, e2, IsPullback.isoPullback_inv_snd, Category.id_comp]
  obtain ⟨E, hE⟩ : ∃ E, E ≫ e = pullback.lift _ _ wl :=
    ⟨pullback.lift _ _ wl ≫ hA.1.isoPullback.inv, by rw [Category.assoc, he, Category.comp_id]⟩
  have h2 : LBIso (L.pull (U.ι ≫ pullback.fst A.hom t)) ((M.pull (pullback.fst B.hom t)).pull (U.ι ≫ Φ.left)) := by
    refine lbIso_pull hL hM E ?_ ?_ hI
    · rw [← e1, ← Category.assoc, hE, pullback.lift_fst]
    · rw [Category.assoc, hΦ, ← e3, ← Category.assoc, hE, ← Category.assoc, he']
  exact LBIso.trans (LB.isLB_pull (LB.isLB_pull hL _) _) (LB.isLB_pull hL _) (LB.isLB_pull (LB.isLB_pull (LB.isLB_pull hM _) _) _)
    (lbIso_pull_pull hL _ _) (LBIso.trans (LB.isLB_pull hL _) (LB.isLB_pull (LB.isLB_pull hM _) _)
      (LB.isLB_pull (LB.isLB_pull (LB.isLB_pull hM _) _) _) h2 (lbIso_pull_pull (LB.isLB_pull hM _) _ _).symm)

theorem glue_wit : (∀ (H : Scheme.{0}) (A B : Over H) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (Φ : A ⟶ B), IsMonHom Φ → IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Out.Rigidified A L → Out.Rigidified B M → (∀ h : H, ∃ W : H.Opens, h ∈ W ∧ LBIso (L.pull (A.hom ⁻¹ᵁ W).ι) ((M.pull Φ.left).pull (A.hom ⁻¹ᵁ W).ι)) → LBIso L (M.pull Φ.left)) → ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left), L.IsLB → M.IsLB → IsAbelianScheme A → IsAbelianScheme B → Out.Rigidified A L → Out.Rigidified B M → ∀ (Z : Scheme.{0}) (𝒰 : Z.OpenCover) (t : Z ⟶ S) (f : pullback A.hom t ⟶ B.left), (∀ i, HomGlue.Wit A B L M (𝒰.f i ≫ t) (HomGlue.pmap A t (𝒰.f i) ≫ f)) → HomGlue.Wit A B L M t f := by
  intro hiso S A B _ _ _ _ L M hL hM hA hB hrA hrB Z 𝒰 t f hw
  have w : f ≫ B.hom = pullback.snd A.hom t ≫ t :=
    pmap_hom_ext A 𝒰 t fun i => wit_w (𝒰.f i) (hw i)
  let Φ : (Over.pullback t).obj A ⟶ (Over.pullback t).obj B :=
    Over.homMk (pullback.lift f (pullback.snd A.hom t) w) (pullback.lift_snd _ _ _)
  have hΦf : Φ.left ≫ pullback.fst B.hom t = f := pullback.lift_fst _ _ _
  have hΦ : IsMonHom Φ := isMonHom_of_cover 𝒰 Φ fun i => isMonHom_pull_of_wit (𝒰.f i) (hw i) Φ hΦf
  have ab_pull (G : Over S) [GrpObj G] (hG : IsAbelianScheme G) :
      IsAbelianScheme ((Over.pullback t).obj G) := by
    letI := hG.comm
    letI := hG.smooth
    letI := hG.proper
    letI := hG.geomConnected
    constructor
    case comm => infer_instance
    case smooth =>
      show Smooth (pullback.snd G.hom t)
      infer_instance
    case proper =>
      show IsProper (pullback.snd G.hom t)
      infer_instance
    case geomConnected =>
      show GeometricallyConnected (pullback.snd G.hom t)
      infer_instance
  have hA' := ab_pull A hA
  have hB' := ab_pull B hB
  haveI : IsCommMonObj ((Over.pullback t).obj A) := hA'.comm
  haveI : IsCommMonObj ((Over.pullback t).obj B) := hB'.comm
  have hI : LBIso (L.pull (pullback.fst A.hom t)) ((M.pull (pullback.fst B.hom t)).pull Φ.left) :=
    hiso Z _ _ _ _ Φ hΦ hA' hB' (LB.isLB_pull hL _) (LB.isLB_pull hM _)
      (GlobalTheory.PolBaseChange.rigidified_pull (isGrpPullback_pullback A t) hrA)
      (GlobalTheory.PolBaseChange.rigidified_pull (isGrpPullback_pullback B t) hrB)
      fun z => ⟨(𝒰.f (𝒰.idx z)).opensRange, Scheme.Hom.mem_opensRange.2 (𝒰.covers z),
        local_iso hL hM (𝒰.f (𝒰.idx z)) (hw _) Φ hΦf⟩
  exact ⟨_, _, inferInstance, inferInstance, _, _, Φ, isGrpPullback_pullback A t, isGrpPullback_pullback B t, hΦ,
    hI, 𝟙 _, Category.id_comp _, Category.id_comp _, (Category.id_comp _).trans hΦf.symm⟩

end GlobalTheory.EndLoc.HomGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomFixRepOfUniversalAlt
section
set_option autoImplicit false
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.EndLoc.HomGlue

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] {L : LB A.left} {M : LB B.left}

theorem Pt.f_congr {Z W : Scheme.{0}} {x y : Pt A B L M Z} (h : x = y) (k : W ⟶ pullback A.hom x.t)
    (k' : W ⟶ pullback A.hom y.t) (h1 : k ≫ pullback.fst _ _ = k' ≫ pullback.fst _ _)
    (h2 : k ≫ pullback.snd _ _ = k' ≫ pullback.snd _ _) : k ≫ x.f = k' ≫ y.f := by
  subst h
  have : k = k' := pullback.hom_ext h1 h2
  subst this
  rfl

theorem homFixRep_of_universal (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (L : LB A.left)
    (M : LB B.left) (hL : L.IsLB) (hM : M.IsLB) (X : Scheme.{0}) (u : HomGlue.Pt A B L M X) :
    (∀ (Z : Scheme.{0}) (x : HomGlue.Pt A B L M Z), ∃! c : Z ⟶ X, u.map hL hM c = x) →
      ∃ (R : HomFixRep A B L M) (e : R.H ≅ X), e.hom ≫ u.t = R.π := by
  intro hu
  obtain ⟨A', B', iA, iB, φA, φB, Φ, hA, hB, hΦ, hI, e, e1, e2, e3⟩ := u.wit
  refine ⟨@HomFixRep.mk S A B _ _ L M X u.t A' iA B' iB φA φB hA hB Φ hΦ hI ?_, Iso.refl X, Category.id_comp _⟩
  intro T t A'' B'' _ _ φA' φB' Φ' hA' hB' hΦ' hI'
  let x : Pt A B L M T := Pt.ofData t A'' B'' φA' φB' Φ' hA' hB' hΦ' hI'
  have hxf : x.f = hA'.1.isoPullback.inv ≫ Φ'.left ≫ φB' := rfl

  have key : ∀ (h : T ⟶ X) (ψA : A''.left ⟶ A'.left), h ≫ u.t = t → ψA ≫ φA = φA' →
      ψA ≫ A'.hom = A''.hom ≫ h → Φ'.left ≫ φB' = ψA ≫ Φ.left ≫ φB → u.map hL hM h = x := by
    intro h ψA ht hψ1 hψ2 hf
    refine Pt.ext' ht ?_
    show pullback.lift (pullback.fst A.hom t) (pullback.snd A.hom t) (by rw [pullback.condition, ht])
      ≫ pmap A u.t h ≫ u.f = (hA'.1.isoPullback.inv ≫ Φ'.left ≫ φB' : pullback A.hom t ⟶ B.left)
    rw [← cancel_epi hA'.1.isoPullback.hom, Iso.hom_inv_id_assoc]
    have hk : hA'.1.isoPullback.hom ≫ pullback.lift (pullback.fst A.hom t) (pullback.snd _ _)
        (by rw [pullback.condition, ht] : _ = _ ≫ h ≫ u.t) ≫ pmap A u.t h = ψA ≫ e := by
      apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst, IsPullback.isoPullback_hom_fst, e1, hψ1]
      · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, e2, hψ2]
        rw [← Category.assoc, IsPullback.isoPullback_hom_snd]
    rw [← Category.assoc, ← Category.assoc, Category.assoc _ _ (pmap A u.t h), hk, Category.assoc, e3, hf]
  obtain ⟨c, hc, hcu⟩ := hu T x
  have hct : c ≫ u.t = t := congrArg Pt.t hc
  have wA : φA' ≫ A.hom = (A''.hom ≫ c) ≫ u.t := by rw [hA'.1.w, Category.assoc, hct]
  have wB : φB' ≫ B.hom = (B''.hom ≫ c) ≫ u.t := by rw [hB'.1.w, Category.assoc, hct]
  let ψA := hA.1.lift φA' (A''.hom ≫ c) wA
  let ψB := hB.1.lift φB' (B''.hom ≫ c) wB
  have hψA1 : ψA ≫ φA = φA' := hA.1.lift_fst _ _ _
  have hψA2 : ψA ≫ A'.hom = A''.hom ≫ c := hA.1.lift_snd _ _ _
  have hψB1 : ψB ≫ φB = φB' := hB.1.lift_fst _ _ _
  have hψB2 : ψB ≫ B'.hom = B''.hom ≫ c := hB.1.lift_snd _ _ _
  have gA : IsGrpPullback A'' A' c ψA := IsGrpPullback.cancel hA (hA'.congr hct.symm hψA1.symm) hψA2
  have gB : IsGrpPullback B'' B' c ψB := IsGrpPullback.cancel hB (hB'.congr hct.symm hψB1.symm) hψB2

  have hfc : Φ'.left ≫ φB' = ψA ≫ e ≫ u.f := by
    have h0 := Pt.f_congr hc
      (pullback.lift φA' A''.hom (by rw [hA'.1.w, hct]) : A''.left ⟶ pullback A.hom (c ≫ u.t))
      (hA'.1.isoPullback.hom : A''.left ⟶ pullback A.hom t)
      ((pullback.lift_fst _ _ _).trans hA'.1.isoPullback_hom_fst.symm)
      ((pullback.lift_snd _ _ _).trans hA'.1.isoPullback_hom_snd.symm)
    have hk : pullback.lift φA' A''.hom (by rw [hA'.1.w, hct]) ≫ pmap A u.t c = ψA ≫ e := by
      apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst, e1, hψA1]
      · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, e2, hψA2]
    change _ ≫ pmap A u.t c ≫ u.f = (hA'.1.isoPullback.hom : A''.left ⟶ pullback A.hom t) ≫
      (hA'.1.isoPullback.inv ≫ Φ'.left ≫ φB' : pullback A.hom t ⟶ B.left) at h0
    rw [Iso.hom_inv_id_assoc, ← Category.assoc, hk, Category.assoc] at h0
    exact h0.symm
  have hcomm : Φ'.left ≫ ψB = ψA ≫ Φ.left := by
    apply hB.1.hom_ext
    · rw [Category.assoc, hψB1, Category.assoc, hfc, e3]
    · rw [Category.assoc, hψB2, ← Category.assoc, Over.w Φ', Category.assoc, Over.w Φ, hψA2]
  refine ⟨c, ⟨hct, ψA, ψB, gA, gB, hψA1, hψB1, hcomm⟩, ?_⟩
  rintro h ⟨ht, χA, χB, kA, kB, kA1, kB1, kcomm⟩
  have hx : u.map hL hM h = x := key h χA ht kA1 kA.1.w (by
    rw [← kB1, ← Category.assoc, kcomm, Category.assoc])
  exact (hcu h hx)

end GlobalTheory.EndLoc.HomGlue
end
end

