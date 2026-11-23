module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.BaseCoefJumpProof
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResEqIff
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0418

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentRankConstOfCharpolyInLocalFunctions
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing Polynomial

namespace GlobalTheory.IdemConstRank

theorem charpoly_of_idem {K : Type} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (h : M * M = M) :
    ∃ b : ℕ, M.charpoly = (X - 1) ^ M.rank * X ^ b := by
  classical
  have hf : IsIdempotentElem (Matrix.toLin' M) := by
    have h2 : Matrix.toLin' (M * M) = Matrix.toLin' M := by rw [h]
    rw [Matrix.toLin'_mul] at h2
    exact h2
  have hc := LinearMap.IsIdempotentElem.isCompl hf
  let e := Submodule.prodEquivOfIsCompl _ _ hc
  have key : e.conj ((1 : Module.End K (LinearMap.range (Matrix.toLin' M))).prodMap
      (0 : Module.End K (LinearMap.ker (Matrix.toLin' M)))) = Matrix.toLin' M := by
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := e.surjective x
    rw [LinearEquiv.conj_apply]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      LinearMap.prodMap_apply, Module.End.one_apply, LinearMap.zero_apply]
    rw [Submodule.coe_prodEquivOfIsCompl', Submodule.coe_prodEquivOfIsCompl', map_add (f := _),
      LinearMap.mem_ker.mp y.2.2, (LinearMap.IsIdempotentElem.mem_range_iff hf).mp y.1.2]
    simp
  refine ⟨Module.finrank K (LinearMap.ker (Matrix.toLin' M)), ?_⟩
  have hcp : M.charpoly = (e.conj ((1 : Module.End K (LinearMap.range (Matrix.toLin' M))).prodMap
      (0 : Module.End K (LinearMap.ker (Matrix.toLin' M))))).charpoly := by
    rw [key, Matrix.charpoly_toLin']
  rw [hcp, LinearEquiv.charpoly_conj, LinearMap.charpoly_prodMap,
    LinearMap.charpoly_one, LinearMap.charpoly_zero, Matrix.rank, ← Matrix.toLin'_apply']

theorem residue_eq {X O : Type} [CommRing O] [IsLocalRing O] (T : Subalgebra O (X → O))
    [IsLocalRing T] (f : X → O) (hf : f ∈ T) (x y : X) :
    IsLocalRing.residue O (f x) = IsLocalRing.residue O (f y) := by
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  by_contra hne
  have hu : IsUnit (f x - f y) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hne
    exact hne
  have ev : ∀ z : X, ∀ t : T, IsUnit t → IsUnit ((t : X → O) z) := fun z t ht =>
    ht.map ((Pi.evalRingHom (fun _ : X => O) z).comp T.val.toRingHom)
  let g : T := ⟨f - algebraMap O (X → O) (f y), T.sub_mem hf (T.algebraMap_mem _)⟩
  let g' : T := algebraMap O T (f x - f y) - g
  have hg : g ∈ nonunits T := fun hg => by
    have := ev y g hg
    simp [g] at this
  have hg' : g' ∈ nonunits T := fun hg => by
    have := ev x g' hg
    simp [g', g] at this
  have hsum : g + g' = algebraMap O T (f x - f y) := by
    simp [g']
  exact IsLocalRing.nonunits_add hg hg' (hsum ▸ hu.map (algebraMap O T))

theorem rootMultiplicity_one {k : Type} [Field k] (a b : ℕ) :
    rootMultiplicity (1 : k) ((X - 1) ^ a * X ^ b) = a := by
  have h1 : ((Polynomial.X : k[X]) - 1) ^ a = (Polynomial.X - Polynomial.C 1) ^ a := by
    rw [map_one]
  have hne : ((Polynomial.X : k[X]) - Polynomial.C 1) ^ a * Polynomial.X ^ b ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (X_sub_C_ne_zero 1)) (pow_ne_zero _ X_ne_zero)
  rw [h1, rootMultiplicity_mul hne, rootMultiplicity_X_sub_C_pow, rootMultiplicity_eq_zero, add_zero]
  simp [IsRoot]

theorem rank_eq_rootMultiplicity {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) O) (h : M * M = M) :
    (M.map (toFr O)).rank = rootMultiplicity 1 (M.charpoly.map (IsLocalRing.residue O)) := by
  obtain ⟨b, hb⟩ := charpoly_of_idem (M.map (toFr O)) (by rw [← Matrix.map_mul, h])
  rw [Matrix.charpoly_map] at hb
  have hinj : Function.Injective (toFr O) := IsFractionRing.injective O (FractionRing O)
  have hM : M.charpoly = ((Polynomial.X : O[X]) - 1) ^ (M.map (toFr O)).rank * Polynomial.X ^ b := by
    apply Polynomial.map_injective _ hinj
    rw [hb]
    simp
  rw [hM]
  simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_one]
  exact (rootMultiplicity_one _ _).symm

theorem rank_const : ∀ {X O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] {n : ℕ} (T : Subalgebra O (X → O)) (e : X → Matrix (Fin n) (Fin n) O), IsLocalRing T → e * e = e → (∀ j : ℕ, (fun x => (e x).charpoly.coeff j) ∈ T) → ∀ x y, ((e x).map (toFr O)).rank = ((e y).map (toFr O)).rank := by
  intro X O _ _ _ n T e hT he hc x y
  have hx := rank_eq_rootMultiplicity (e x) (congrFun he x)
  have hy := rank_eq_rootMultiplicity (e y) (congrFun he y)
  have hp : (e x).charpoly.map (IsLocalRing.residue O) = (e y).charpoly.map (IsLocalRing.residue O) := by
    ext j
    rw [Polynomial.coeff_map, Polynomial.coeff_map]
    exact residue_eq T (fun z => (e z).charpoly.coeff j) (hc j) x y
  rw [hx, hy, hp]

end GlobalTheory.IdemConstRank
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InclIntegral
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.BaseCoef

variable {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G]

abbrev incl {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) : ↥LL.1 →ₐ[ℚ_[l]] ↥LL'.1 :=
  IntermediateField.inclusion h

def IsLatBasis {LL : FinExt l} (T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) {k : ℕ}
    (b : Module.Basis (Fin k) ↥LL.1 T.V) : Prop :=
  (∀ i, b i ∈ T.L.T) ∧ ∀ x ∈ T.L.T, ∀ i, b.repr x i ∈ OL LL

def matRep {LL : FinExt l} (T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) {k : ℕ}
    (b : Module.Basis (Fin k) ↥LL.1 T.V) : G →* Matrix (Fin k) (Fin k) ↥LL.1 :=
  (LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp T.ρ

def matRepExt {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) (T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) {k : ℕ}
    (b : Module.Basis (Fin k) ↥LL.1 T.V) : G →* Matrix (Fin k) (Fin k) ↥LL'.1 :=
  ((incl h).mapMatrix : Matrix (Fin k) (Fin k) ↥LL.1 →ₐ[ℚ_[l]] Matrix (Fin k) (Fin k) ↥LL'.1).toRingHom.toMonoidHom.comp
    (matRep T b)

def intVec (LL' : FinExt l) (k : ℕ) : Submodule ↥(OL LL') (Fin k → ↥LL'.1) where
  carrier := {v | ∀ i, v i ∈ OL LL'}
  add_mem' := fun ha hb i => add_mem (ha i) (hb i)
  zero_mem' := fun _ => zero_mem _
  smul_mem' := fun c v hv i => by
    rw [Pi.smul_apply, Subalgebra.smul_def]
    exact mul_mem c.2 (hv i)

theorem incl_integral {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) {x : ↥LL.1} (hx : x ∈ OL LL) :
    incl h x ∈ OL LL' := by
  have hx' : IsIntegral ℤ_[l] x := hx
  exact hx'.map ((incl h).restrictScalars ℤ_[l])

theorem rep_apply {F : Type} [Field F] {k : ℕ} (M : G →* Matrix (Fin k) (Fin k) F) (g : G) (x : Fin k → F) :
    CJ.rep M g x = (M g).mulVec x := rfl

set_option synthInstance.maxHeartbeats 400000

def intVecEquiv (LL' : FinExt l) (k : ℕ) : ↥(intVec LL' k) ≃ₗ[↥(OL LL')] (Fin k → ↥(OL LL')) where
  toFun v := fun i => ⟨(v : Fin k → ↥LL'.1) i, v.2 i⟩
  invFun w := ⟨fun i => (w i : ↥LL'.1), fun i => (w i).2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem repr_integral {LL : FinExt l} {T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)} {k : ℕ}
    {b : Module.Basis (Fin k) ↥LL.1 T.V} (hb : IsLatBasis T b) (g : G) (i j : Fin k) :
    matRep T b g i j ∈ OL LL := by
  rw [matRep, MonoidHom.comp_apply]
  change LinearMap.toMatrix b b (T.ρ g) i j ∈ OL LL
  rw [LinearMap.toMatrix_apply]
  exact hb.2 _ (T.L.stable g _ (hb.1 j)) i

abbrev extLat {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) (T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) {k : ℕ}
    (b : Module.Basis (Fin k) ↥LL.1 T.V) (hb : IsLatBasis T b) : LocLat G ℚ_[l] ↥LL'.1 ↥(OL LL') where
  V := Fin k → ↥LL'.1
  ρ := CJ.rep (matRepExt h T b)
  cont x := by
    refine continuous_pi fun i => ?_
    simp only [rep_apply, Matrix.mulVec, dotProduct]
    refine continuous_finsetSum _ fun j _ => Continuous.mul ?_ continuous_const
    have h1 : Continuous fun g => b.coord i (T.ρ g (b j)) :=
      (IsModuleTopology.continuous_of_linearMap (b.coord i)).comp (T.cont (b j))
    have h2 : Continuous (incl h) := continuous_subtype_val.subtype_mk _
    refine (h2.comp h1).congr fun g => ?_
    simp [matRepExt, matRep, LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply]
  L :=
    { T := intVec LL' k
      stable := fun g x hx i => by
        simp only [rep_apply, Matrix.mulVec, dotProduct]
        refine Subalgebra.sum_mem _ fun j _ => Subalgebra.mul_mem _ ?_ (hx j)
        exact incl_integral h (repr_integral hb g i j)
      fg := by
        haveI : Module.Finite ↥(OL LL') ↥(intVec LL' k) := Module.Finite.equiv (intVecEquiv LL' k).symm
        exact Module.Finite.iff_fg.1 inferInstance
      free := Module.Free.of_equiv (intVecEquiv LL' k).symm
      span := by
        rw [eq_top_iff, ← (Pi.basisFun ↥LL'.1 (Fin k)).span_eq]
        refine Submodule.span_mono ?_
        rintro _ ⟨i, rfl⟩ j
        rw [Pi.basisFun_apply]
        by_cases hij : i = j
        · subst hij; simp [one_mem]
        · simp [Pi.single_apply, Ne.symm hij, zero_mem] }

theorem hom_integral {LL : FinExt l} {T₁ T₂ : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)} {k₁ k₂ : ℕ}
    {b₁ : Module.Basis (Fin k₁) ↥LL.1 T₁.V} {b₂ : Module.Basis (Fin k₂) ↥LL.1 T₂.V}
    (hb₁ : IsLatBasis T₁ b₁) (hb₂ : IsLatBasis T₂ b₂) (F : LatHom T₁.L T₂.L) (i : Fin k₂) (j : Fin k₁) :
    LinearMap.toMatrix b₁ b₂ F.f i j ∈ OL LL := by
  rw [LinearMap.toMatrix_apply]
  exact hb₂.2 _ (F.T_le _ (hb₁.1 j)) i

def extMat {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) {T₁ T₂ : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)} {k₁ k₂ : ℕ}
    (b₁ : Module.Basis (Fin k₁) ↥LL.1 T₁.V) (b₂ : Module.Basis (Fin k₂) ↥LL.1 T₂.V) (F : LatHom T₁.L T₂.L) :
    Matrix (Fin k₂) (Fin k₁) ↥LL'.1 :=
  (LinearMap.toMatrix b₁ b₂ F.f).map (incl h)

set_option maxHeartbeats 1000000 in
theorem extMat_comm {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) {T₁ T₂ : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)} {k₁ k₂ : ℕ}
    (b₁ : Module.Basis (Fin k₁) ↥LL.1 T₁.V) (b₂ : Module.Basis (Fin k₂) ↥LL.1 T₂.V) (F : LatHom T₁.L T₂.L)
    (g : G) : extMat h b₁ b₂ F * matRepExt h T₁ b₁ g = matRepExt h T₂ b₂ g * extMat h b₁ b₂ F := by
  have e1 : matRepExt h T₁ b₁ g = (LinearMap.toMatrix b₁ b₁ (T₁.ρ g)).map (incl h) := rfl
  have e2 : matRepExt h T₂ b₂ g = (LinearMap.toMatrix b₂ b₂ (T₂.ρ g)).map (incl h) := rfl
  have key : LinearMap.toMatrix b₁ b₂ F.f * LinearMap.toMatrix b₁ b₁ (T₁.ρ g) =
      LinearMap.toMatrix b₂ b₂ (T₂.ρ g) * LinearMap.toMatrix b₁ b₂ F.f := by
    have c1 := LinearMap.toMatrix_comp b₁ b₁ b₂ F.f (T₁.ρ g)
    have c2 := LinearMap.toMatrix_comp b₁ b₂ b₂ (T₂.ρ g) F.f
    have hc : F.f ∘ₗ T₁.ρ g = T₂.ρ g ∘ₗ F.f := LinearMap.ext fun y => F.equiv g y
    rw [← c1, ← c2, hc]
  refine Matrix.ext fun i j => ?_
  have := congrArg (fun M => incl h (M i j)) key
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, map_sum, map_mul] at this
  simpa only [e1, e2, Matrix.mul_apply, extMat, Matrix.map_apply] using this

def extHom {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) {T₁ T₂ : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)} {k₁ k₂ : ℕ}
    {b₁ : Module.Basis (Fin k₁) ↥LL.1 T₁.V} {b₂ : Module.Basis (Fin k₂) ↥LL.1 T₂.V}
    (hb₁ : IsLatBasis T₁ b₁) (hb₂ : IsLatBasis T₂ b₂) (F : LatHom T₁.L T₂.L) :
    LatHom (extLat h T₁ b₁ hb₁).L (extLat h T₂ b₂ hb₂).L where
  f := Matrix.toLin' (extMat h b₁ b₂ F)
  equiv g x := by
    change (extMat h b₁ b₂ F).mulVec ((matRepExt h T₁ b₁ g).mulVec x) =
      (matRepExt h T₂ b₂ g).mulVec ((extMat h b₁ b₂ F).mulVec x)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, extMat_comm]
  cont := LinearMap.continuous_on_pi _
  T_le x hx i := by
    change (extMat h b₁ b₂ F).mulVec x i ∈ OL LL'
    simp only [Matrix.mulVec, dotProduct, extMat, Matrix.map_apply]
    exact Subalgebra.sum_mem _ fun j _ => Subalgebra.mul_mem _ (incl_integral h (hom_integral hb₁ hb₂ F i j)) (hx j)

def mapSig {I LL LL' : Type} [Group I] [Field LL] [Field LL'] (f : LL →+* LL') (Sig : Finset (I →* LLˣ)) :
    Finset (I →* LL'ˣ) := by
  classical
  exact Sig.image fun a => (Units.map (f : LL →* LL')).comp a

end GlobalTheory.BaseCoef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InclLSmulCoord
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.BKGal

variable {l : ℕ} [Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e)
  {ι : Type} [Fintype ι] [DecidableEq ι] {G : Type} [Group G] [TopologicalSpace G]

theorem inclL_smul_coord (P : PhiMod O K l e a ι) (m : OA l O) (c : ι → OA l O) :
    inclL t ϖ P (fun i => m * c i) = inclO l O m • inclL t ϖ P c := by
  rw [inclL_apply, inclL_apply]
  have h : (fun i => inclO l O (m * c i)) = inclO l O m • fun i => inclO l O (c i) :=
    funext fun i => by simp only [map_mul, Pi.smul_apply, smul_eq_mul]
  rw [h, Matrix.mulVec_smul]

theorem IsCrisVal.sub {P : PhiMod O K l e a ι} {T : LocLat G ℚ_[l] K O}
    {jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T} {w w' : ι → OW l O} {b b' : TW (OB l O) T}
    (h : IsCrisVal t ϖ P jB w b) (h' : IsCrisVal t ϖ P jB w' b') : IsCrisVal t ϖ P jB (w - w') (b - b') := by
  obtain ⟨m, c, hu, hc, hb⟩ := h
  obtain ⟨m', c', hu', hc', hb'⟩ := h'
  refine ⟨m * m', fun i => m' * c i - m * c' i, by rw [map_mul]; exact hu.mul hu', ?_, ?_⟩
  · have e1 : (fun i => m' * c i - m * c' i) = (fun i => m' * c i) - (fun i => m * c' i) := rfl
    rw [e1, map_sub, inclL_smul_coord, inclL_smul_coord, ← hc, ← hc', smul_sub, smul_smul, smul_smul, map_mul,
      mul_comm (inclO l O m')]
  · have e2 : (fun i => toB l O (m' * c i - m * c' i)) =
        toB l O m' • (fun i => toB l O (c i)) - toB l O m • (fun i => toB l O (c' i)) :=
      funext fun i => by simp only [map_sub, map_mul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [e2, map_sub, map_smul, map_smul, ← hb, ← hb', smul_sub, smul_smul, smul_smul, map_mul,
      mul_comm (toB l O m')]

end GlobalTheory.BKGal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaConjMem
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.BKGal GlobalTheory.Per

namespace GlobalTheory.InertiaConj

theorem norm_aut_eq {l : ℕ} [Fact l.Prime] (τ : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) (x : PadicAlgCl l) :
    ‖τ x‖ = ‖x‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq]
  exact (spectralNorm_eq_of_equiv τ x).symm

theorem inertia_conj_mem : ∀ (l : ℕ) [Fact l.Prime] (g τ : Gl l), g ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l) →
    τ⁻¹ * g * τ ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l) := by
  intro l _ g τ hg
  have hS : ∀ σ : Gl l, (∀ x : Om l, ‖x‖ ≤ 1 → ‖(σ : GQ l) x - x‖ < 1) →
      ∀ x : Om l, ‖x‖ ≤ 1 → ‖((τ⁻¹ * σ * τ : Gl l) : GQ l) x - x‖ < 1 := by
    intro σ hσ x hx
    have hτx : ‖(τ : GQ l) x‖ ≤ 1 := by rw [norm_aut_eq]; exact hx
    have h1 := hσ ((τ : GQ l) x) hτx
    have h2 : ((τ⁻¹ * σ * τ : Gl l) : GQ l) x - x =
        ((τ : GQ l).symm) ((σ : GQ l) ((τ : GQ l) x) - (τ : GQ l) x) := by
      simp [map_sub]
    rw [h2, norm_aut_eq]
    exact h1
  unfold IK at hg ⊢
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact Subgroup.subset_closure (hS x hx)
  | one => simp
  | mul x y _ _ hx hy =>
    have : τ⁻¹ * (x * y) * τ = (τ⁻¹ * x * τ) * (τ⁻¹ * y * τ) := by group
    rw [this]; exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have : τ⁻¹ * x⁻¹ * τ = (τ⁻¹ * x * τ)⁻¹ := by group
    rw [this]; exact Subgroup.inv_mem _ hx

end GlobalTheory.InertiaConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaCyclic
section
noncomputable section
namespace GlobalTheory.TameInertiaCyclic
open _root_.Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc GlobalTheory.MemLoc.FrobLaws

variable {l : ℕ} [hl : Fact l.Prime]

theorem exists_pow_norm (K : FinExt l) :
    ∃ d : ℕ, 0 < d ∧ ∀ x ∈ K.1, x ≠ 0 → ∃ a : ℤ, ‖x‖ ^ d = (l : ℝ) ^ a := by
  haveI := K.2
  refine ⟨Module.finrank ℚ_[l] ↥K.1, Module.finrank_pos, fun x hxK hx => ?_⟩
  have e := spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow ℚ_[l] (PadicAlgCl l) x
  rw [PadicAlgCl.spectralNorm_eq] at e
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : (minpoly ℚ_[l] x).coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hi hx
  have hn := minpoly.natDegree_pos hi
  have hd : (minpoly ℚ_[l] x).natDegree ∣ Module.finrank ℚ_[l] ↥K.1 := by
    have := minpoly.degree_dvd (K := ℚ_[l]) (x := (⟨x, hxK⟩ : ↥K.1)) (Algebra.IsIntegral.isIntegral _)
    rwa [IntermediateField.minpoly_eq] at this
  obtain ⟨c, hc⟩ := hd
  refine ⟨-((minpoly ℚ_[l] x).coeff 0).valuation * c, ?_⟩
  rw [hc, pow_mul, e, one_div, Real.rpow_inv_natCast_pow (norm_nonneg _) hn.ne',
    Padic.norm_eq_zpow_neg_valuation h0, zpow_mul, zpow_natCast]

theorem exists_gen (K : FinExt l) :
    ∃ π ∈ K.1, π ≠ 0 ∧ ∀ x ∈ K.1, x ≠ 0 → ∃ k : ℤ, ‖x‖ = ‖π ^ k‖ := by
  obtain ⟨d, hd, H⟩ := exists_pow_norm K
  have hl0 : (l : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hl.out.ne_zero
  let S : AddSubgroup ℤ :=
    { carrier := {n | ∃ x ∈ K.1, x ≠ 0 ∧ ‖x‖ ^ d = (l : ℝ) ^ n}
      add_mem' := by
        rintro a b ⟨x, hx, hx0, ex⟩ ⟨y, hy, hy0, ey⟩
        exact ⟨x * y, mul_mem hx hy, mul_ne_zero hx0 hy0, by
          rw [norm_mul, mul_pow, ex, ey, zpow_add₀ hl0]⟩
      zero_mem' := ⟨1, one_mem _, one_ne_zero, by simp⟩
      neg_mem' := by
        rintro a ⟨x, hx, hx0, ex⟩
        exact ⟨x⁻¹, inv_mem hx, inv_ne_zero hx0, by rw [norm_inv, inv_pow, ex, zpow_neg]⟩ }
  haveI : IsAddCyclic S := AddSubgroup.isAddCyclic S
  obtain ⟨f, hf⟩ := IsAddCyclic.exists_zsmul_surjective (G := S)
  have hfS : (f : ℤ) ∈ S := f.property
  obtain ⟨π, hπ, hπ0, eπ⟩ := hfS
  refine ⟨π, hπ, hπ0, fun x hx hx0 => ?_⟩
  obtain ⟨a, ha⟩ := H x hx hx0
  have haS : a ∈ S := ⟨x, hx, hx0, ha⟩
  obtain ⟨k, hk⟩ := hf ⟨a, haS⟩
  have hk' : k • (f : ℤ) = a := congrArg Subtype.val hk
  subst a
  refine ⟨k, (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) hd.ne').1 ?_⟩
  rw [ha, norm_zpow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, eπ, ← zpow_mul,
    smul_eq_mul, mul_comm]

theorem fix_of_near (K : FinExt l) (g : GQ l) (hst : ∀ x ∈ K.1, g x ∈ K.1)
    (hnear : ∀ x ∈ K.1, x ≠ 0 → ‖g x - x‖ < ‖x‖) {N : ℕ} (hN : ¬ l ∣ N)
    (hgN : ∀ x ∈ K.1, (g ^ N) x = x) (y : Om l) (hy : y ∈ K.1) : g y = y := by
  by_contra hne
  have hx0 : g y - y ≠ 0 := sub_ne_zero.2 hne
  have hxK : g y - y ∈ K.1 := sub_mem (hst y hy) hy
  set x := g y - y with hx
  have h1 : ∀ i : ℕ, ‖(g ^ i) x - x‖ < ‖x‖ := by
    intro i
    induction i with
    | zero => simpa using hx0
    | succ i ih =>
      have e : (g ^ (i + 1)) x - x = (g ^ i) (g x - x) + ((g ^ i) x - x) := by
        rw [pow_succ, AlgEquiv.mul_apply, map_sub (g ^ i)]; ring
      rw [e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ih)
      rw [norm_gal]; exact hnear x hxK hx0
  have h2 : ∀ k : ℕ, ‖((g ^ k) y - y) - (k : Om l) * x‖ < ‖x‖ := by
    intro k
    induction k with
    | zero => simpa using hx0
    | succ k ih =>
      have e : ((g ^ (k + 1)) y - y) - ((k + 1 : ℕ) : Om l) * x =
          (((g ^ k) y - y) - (k : Om l) * x) + ((g ^ k) x - x) := by
        rw [pow_succ, AlgEquiv.mul_apply, hx, map_sub]; push_cast; ring
      rw [e]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ih (h1 k))
  have hmn : ‖(N : Om l)‖ = 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends]
    exact Padic.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd hl.out).2 hN)
  have := h2 N
  rw [hgN y hy, sub_self, zero_sub, norm_neg, norm_mul, hmn, one_mul] at this
  exact lt_irrefl _ this

def ratio (g : GQ l) (x : Om l) : OO l :=
  ⟨g x / x, by
    show ‖g x / x‖ ≤ 1
    rw [norm_div, norm_gal]; exact div_self_le_one _⟩

theorem ratio_mul (g : GQ l) (x y : Om l) : ratio g (x * y) = ratio g x * ratio g y :=
  Subtype.ext (by
    show g (x * y) / (x * y) = g x / x * (g y / y)
    rw [map_mul, mul_div_mul_comm])

theorem res_ratio_iff (g : GQ l) {x : Om l} (hx : x ≠ 0) :
    res (ratio g x) = 1 ↔ ‖g x - x‖ < ‖x‖ := by
  rw [← map_one (res (l := l)), res_eq_iff]
  show ‖g x / x - 1‖ < 1 ↔ _
  have : g x / x - 1 = (g x - x) / x := by field_simp
  rw [this, norm_div, div_lt_one (norm_pos_iff.2 hx)]

theorem res_ratio_zpow (g : GQ l) {x : Om l} (hx : x ≠ 0) (h : res (ratio g x) = 1) (k : ℤ) :
    res (ratio g (x ^ k)) = 1 := by
  induction k using Int.induction_on with
  | zero => rw [res_ratio_iff g (by simp)]; simp
  | succ k ih => rw [zpow_add_one₀ hx, ratio_mul, map_mul, ih, h, one_mul]
  | pred k ih =>
    have e : x ^ (-(k : ℤ)) = x ^ (-(k : ℤ) - 1) * x := by
      rw [← zpow_add_one₀ hx, sub_add_cancel]
    rwa [e, ratio_mul, map_mul, h, mul_one] at ih

theorem map_mem_Kur (g : GQ l) {c : Om l} (hc : c ∈ MaximalUnramifiedExtension l) : g c ∈ MaximalUnramifiedExtension l := by
  unfold MaximalUnramifiedExtension at hc
  induction hc using IntermediateField.adjoin_induction with
  | mem x hx =>
    obtain ⟨m, hm, hlm, hx⟩ := hx
    exact IntermediateField.subset_adjoin _ _ ⟨m, hm, hlm, by rw [← map_pow, hx, map_one]⟩
  | algebraMap x => rw [g.commutes]; exact (MaximalUnramifiedExtension l).algebraMap_mem x
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact (MaximalUnramifiedExtension l).add_mem hx hy
  | inv x _ hx => rw [map_inv₀]; exact (MaximalUnramifiedExtension l).inv_mem hx
  | mul x y _ _ hx hy => rw [map_mul]; exact (MaximalUnramifiedExtension l).mul_mem hx hy

open _root_.Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

end GlobalTheory.TameInertiaCyclic
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IotaOQContinuousInjective
section
namespace GlobalTheory.TypeLeaf

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain


open Polynomial NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.TypeLeaf.iotaOQ_continuous_injective (D : _root_.Formalism.BasicNotions.D7) (i : D.nd.Loc) :
    Continuous (_root_.Formalism.MainNotions.N.iotaOQ D.nd D.naut i) ∧ Function.Injective (_root_.Formalism.MainNotions.N.iotaOQ D.nd D.naut i) := by
  refine ⟨_root_.GlobalTheory.CoeffEmbedding.continuous_iotaOQ _ _ _ D.nd D.naut i, ?_⟩
  unfold _root_.Formalism.MainNotions.N.iotaOQ
  exact (D.naut.iotaQ i).injective.comp (IsFractionRing.injective _ _)

end GlobalTheory.TypeLeaf
end

