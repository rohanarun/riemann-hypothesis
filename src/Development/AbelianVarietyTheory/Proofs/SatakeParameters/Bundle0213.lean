module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0050
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLetterHomComp
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolyWeilDelignePotSemistableEnlargeCoefficie
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0579
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0329
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0202
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0008
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.FrobeniusOrbits.HostCorollaries
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0206
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0205
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0030

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPeriodProductEqOfInvertibleCharacter
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.WeilDeligne
open scoped TensorProduct
open GlobalTheory.Pst.TwistLetters

noncomputable section

namespace GlobalTheory.Pst.TwistLetters.Invert

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {L : FinExt l}
  {V : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V]

theorem mulB_assoc (y y' : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) (w : V ⊗[ℚ_[l]] Bst P) :
    mulB P V y (mulB P V y' w) = mulB P V (mulB P (Fin 1 → ↥L.1) y y') w := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    induction y' using TensorProduct.induction_on with
    | zero => simp
    | tmul a' b' =>
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul v c =>
        rw [mulB_tmul, mulB_tmul, mulB_tmul, mulB_tmul, Pi.smul_apply, smul_eq_mul, mul_smul, mul_assoc]
      | add w w' hw hw' => simp only [map_add (f := _), hw, hw']
    | add y y' hy hy' => simp only [map_add (f := _), LinearMap.add_apply, hy, hy']
  | add y y' hy hy' => simp only [map_add (f := _), LinearMap.add_apply, hy, hy']

theorem mulB_comm (y y' : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) :
    mulB P (Fin 1 → ↥L.1) y y' = mulB P (Fin 1 → ↥L.1) y' y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    induction y' using TensorProduct.induction_on with
    | zero => simp
    | tmul a' b' =>
      rw [mulB_tmul, mulB_tmul, mul_comm b b']
      congr 1
      funext i
      rw [Subsingleton.elim i 0]
      simp [mul_comm]
    | add y y' hy hy' => simp only [map_add (f := _), LinearMap.add_apply, hy, hy']
  | add y y' hy hy' => simp only [map_add (f := _), LinearMap.add_apply, hy, hy']

theorem one_mulB (w : V ⊗[ℚ_[l]] Bst P) :
    mulB P V ((fun _ => (1 : ↥L.1)) ⊗ₜ (1 : Bst P)) w = w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul v c => rw [mulB_tmul, one_smul, one_mul]
  | add w w' hw hw' => simp only [map_add (f := _), hw, hw']

variable {K : FinExt l}

theorem stRep_twist (ρs ρt : Representation ↥L.1 ↥(GK K) V) (χ : ↥(GK K) → ↥L.1)
    (ht : ∀ g v, ρt g v = χ g • ρs g v) (g : ↥(GK K)) (w : V ⊗[ℚ_[l]] Bst P) :
    stRep P ρt g w = χ g • stRep P ρs g w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul v c => rw [stRep_tmul, stRep_tmul, ht, TensorProduct.smul_tmul']
  | add w w' hw hw' => simp only [map_add (f := _), smul_add, hw, hw']

theorem stRep_trivial_one (g : ↥(GK K)) :
    stRep P (Representation.trivial ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) g ((fun _ => (1 : ↥L.1)) ⊗ₜ (1 : Bst P)) =
      (fun _ => (1 : ↥L.1)) ⊗ₜ (1 : Bst P) := by
  rw [stRep_tmul, map_one]
  rfl

end GlobalTheory.Pst.TwistLetters.Invert


set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 200000 in
open GlobalTheory.Pst.TwistLetters.Invert in
theorem GlobalTheory.Pst.TwistLetters.exists_dmul_eq_of_inv : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K L : FinExt l} {V : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V] (ρs ρt : Representation ↥L.1 ↥(GK K) V) (ρm : Representation ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) (χ : ↥(GK K) → ↥L.1) (hm : ∀ g v, ρm g v = χ g • v) (ht : ∀ g v, ρt g v = χ g • ρs g v) (y : ↥(Dpst P ρm)) (y' : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P), GlobalTheory.Pst.TwistLetters.mulB P (Fin 1 → ↥L.1) y' (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) = (fun _ => (1 : ↥L.1)) ⊗ₜ (1 : Bst P) → ∀ z : ↥(Dpst P ρt), ∃ x : ↥(Dpst P ρs), GlobalTheory.Pst.TwistLetters.dmul P ρs ρt ρm χ hm ht x y = z := by
  intro l _ P K L V _ _ _ _ ρs ρt ρm χ hm ht y y' hinv z
  have hmτ : ∀ g w, stRep P ρm g w =
      χ g • stRep P (Representation.trivial ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) g w :=
    stRep_twist _ ρm χ (fun g v => by rw [hm]; rfl)
  have hτmul : ∀ g (a w : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P),
      stRep P (Representation.trivial ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) g (mulB P (Fin 1 → ↥L.1) a w) =
        mulB P (Fin 1 → ↥L.1) (stRep P (Representation.trivial ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) g a)
          (stRep P (Representation.trivial ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) g w) := fun g a w =>
    stRep_mulB _ _ _ (fun _ => (1 : ↥L.1)) (fun _ _ => by rw [one_smul]; rfl)
      (fun _ _ => by rw [one_smul]) g a w
  have hsmul : ∀ g (a : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) (w : V ⊗[ℚ_[l]] Bst P),
      stRep P ρs g (mulB P V a w) =
        mulB P V (stRep P (Representation.trivial ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) g a) (stRep P ρs g w) :=
    fun g a w => stRep_mulB ρs ρs _ (fun _ => (1 : ↥L.1)) (fun _ _ => by rw [one_smul]; rfl)
      (fun _ _ => by rw [one_smul]) g a w
  have hτe := stRep_trivial_one (P := P) (L := L) (K := K)
  have hone : ∀ w : V ⊗[ℚ_[l]] Bst P, mulB P V ((fun _ => (1 : ↥L.1)) ⊗ₜ (1 : Bst P)) w = w := one_mulB
  have hone' : ∀ w : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P,
      mulB P (Fin 1 → ↥L.1) ((fun _ => (1 : ↥L.1)) ⊗ₜ (1 : Bst P)) w = w := one_mulB
  have hχ : ∀ g, χ g ≠ 0 := by
    intro g h0
    have h1 : ρm (g⁻¹ * g) (fun _ => (1 : ↥L.1)) = fun _ => 1 := by simp
    rw [map_mul, Module.End.mul_apply, hm, hm, h0] at h1
    have := congrFun h1 0
    simp at this
  have hcomm1 : ∀ a : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P, mulB P (Fin 1 → ↥L.1) a ((fun _ => (1 : ↥L.1)) ⊗ₜ (1 : Bst P) : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) = a := fun a => by
    rw [mulB_comm, hone']
  obtain ⟨K₁, h₁⟩ := (mem_Dpst P ρm).mp y.2
  obtain ⟨K₂, h₂⟩ := (mem_Dpst P ρt).mp z.2
  have hx : mulB P V y' (z : V ⊗[ℚ_[l]] Bst P) ∈ Dpst P ρs := by
    refine (mem_Dpst P ρs).mpr ⟨supExt K₁ K₂, fun g hg => ?_⟩
    have hy := h₁ g (GK_le (K' := supExt K₁ K₂) le_sup_left hg)
    have hz := h₂ g (GK_le (K' := supExt K₁ K₂) le_sup_right hg)
    have hc := hχ g
    have hτy : stRep P (Representation.trivial ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) g (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) = (χ g)⁻¹ • (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) := by
      rw [hmτ] at hy
      conv_rhs => rw [← hy]
      rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    have hprod : mulB P (Fin 1 → ↥L.1) (stRep P (Representation.trivial ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) g y') (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) = χ g • ((fun _ => (1 : ↥L.1)) ⊗ₜ (1 : Bst P) : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) := by
      have h3 := congrArg (stRep P (Representation.trivial ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) g) hinv
      rw [hτmul, hτy, hτe, mulB_smul] at h3
      rw [← h3, smul_smul, mul_inv_cancel₀ hc, one_smul]
    have hτy' : stRep P (Representation.trivial ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) g y' = χ g • y' := by
      calc stRep P (Representation.trivial ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) g y' = mulB P (Fin 1 → ↥L.1) ((fun _ => (1 : ↥L.1)) ⊗ₜ (1 : Bst P) : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) (stRep P (Representation.trivial ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) g y') := by rw [hone']
        _ = mulB P (Fin 1 → ↥L.1) (mulB P (Fin 1 → ↥L.1) y' (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P)) (stRep P (Representation.trivial ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) g y') := by rw [hinv]
        _ = mulB P (Fin 1 → ↥L.1) y' (mulB P (Fin 1 → ↥L.1) (stRep P (Representation.trivial ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) g y') (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P)) := by
          rw [← mulB_assoc, mulB_comm (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P)]
        _ = χ g • y' := by rw [hprod, mulB_smul, hcomm1]
    have hsz : stRep P ρs g (z : V ⊗[ℚ_[l]] Bst P) = (χ g)⁻¹ • (z : V ⊗[ℚ_[l]] Bst P) := by
      rw [stRep_twist ρs ρt χ ht] at hz
      conv_rhs => rw [← hz]
      rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [hsmul, hτy', hsz, mulB_smul, mulB_smul_left, smul_smul, inv_mul_cancel₀ hc, one_smul]
  refine ⟨⟨_, hx⟩, Subtype.ext ?_⟩
  rw [coe_dmul, mulB_assoc, mulB_comm, hinv, hone]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPlaceParahoricSubgroupCharacter
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.ParaLevel

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem trivOutside_one (T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))) :
    TrivOutside T (1 : GAf L n) := by
  intro w _
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem detDD_one (s : SplitPlace L) (r : ℕ) :
    NG.detDD s r (1 : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) = 1 := by
  unfold NG.detDD
  have : (Matrix.of fun a b : {x : Fin n // r ≤ x.val} =>
      ((1 : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) :
        Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) a.1 b.1) = 1 := by
    ext a b
    simp [Matrix.one_apply, Subtype.ext_iff]
  rw [this, Matrix.det_one]

theorem continuous_detDD (s : SplitPlace L) (r : ℕ) :
    Continuous (NG.detDD (n := n) s r) := by
  unfold NG.detDD
  refine Continuous.matrix_det ?_
  refine continuous_pi fun a => continuous_pi fun b => ?_
  exact (Units.continuous_val (M := Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L)))).matrix_elem a.1 b.1

section main
variable (s : SplitPlace L) (r : ℕ) (J : Subgroup (GAf L n)) (χ : J →* ℂˣ)
  (ξ : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ)

def paraSub (hP : NG.LevelPara J χ s r ξ) :
    Subgroup (GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) where
  carrier := {g | NG.ParaRT s r g}
  one_mem' := by
    have h := (hP.mem 1 (trivOutside_one _)).1 J.one_mem
    change NG.ParaRT s r 1
    rw [map_one] at h
    exact h
  mul_mem' := by
    intro g h hg hh
    obtain ⟨x, hx, rfl⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s g
    obtain ⟨y, hy, rfl⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s h
    have hxy := GlobalTheory.SatInd.CosetFin.trivOutside_mul hx hy
    rw [← map_mul]
    exact (hP.mem _ hxy).1 (J.mul_mem ((hP.mem x hx).2 hg) ((hP.mem y hy).2 hh))
  inv_mem' := by
    intro g hg
    obtain ⟨x, hx, rfl⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s g
    have hi := GlobalTheory.SatInd.CosetFin.trivOutside_inv hx
    show NG.ParaRT s r (s.loc n x)⁻¹
    rw [← map_inv]
    exact (hP.mem _ hi).1 (J.inv_mem ((hP.mem x hx).2 hg))

end main
end GlobalTheory.ParaLevel

namespace GlobalTheory.ParaLevel
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
section main2
variable {s : SplitPlace L} {r : ℕ} {J : Subgroup (GAf L n)} {χ : J →* ℂˣ}
  {ξ : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ}

def lift (s : SplitPlace L) (g : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) : GAf L n :=
  (GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s g).choose

theorem lift_triv (g : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) :
    TrivOutside {s.v} (lift s g) :=
  (GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s g).choose_spec.1

theorem loc_lift (g : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) :
    s.loc n (lift s g) = g :=
  (GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s g).choose_spec.2

theorem lift_mem (hP : NG.LevelPara J χ s r ξ) (g : paraSub s r J χ ξ hP) : lift s g.1 ∈ J :=
  (hP.mem _ (lift_triv g.1)).2 (by rw [loc_lift]; exact g.2)

def thetaFun (hP : NG.LevelPara J χ s r ξ) (g : paraSub s r J χ ξ hP) : ℂˣ :=
  χ ⟨lift s g.1, lift_mem hP g⟩

theorem chi_eq (hP : NG.LevelPara J χ s r ξ) (κ : GAf L n) (hκ : TrivOutside {s.v} κ) (hJ : κ ∈ J)
    (h : s.loc n κ ∈ paraSub s r J χ ξ hP) : χ ⟨κ, hJ⟩ = thetaFun hP ⟨s.loc n κ, h⟩ := by
  unfold thetaFun
  set κ₀ := lift s (s.loc n κ) with hκ₀
  have h0 : κ₀ ∈ J := lift_mem hP ⟨s.loc n κ, h⟩
  have ht : TrivOutside {s.v} (κ * κ₀⁻¹) :=
    GlobalTheory.SatInd.CosetFin.trivOutside_mul hκ (GlobalTheory.SatInd.CosetFin.trivOutside_inv (lift_triv _))
  have hl : s.loc n (κ * κ₀⁻¹) = 1 := by
    rw [map_mul, map_inv, hκ₀, loc_lift, mul_inv_cancel]
  have hδ : κ * κ₀⁻¹ ∈ J := J.mul_mem hJ (J.inv_mem h0)
  have hc : χ ⟨κ * κ₀⁻¹, hδ⟩ = 1 := by
    rw [hP.chr _ hδ ht 1 (by rw [hl, detDD_one]; rfl), map_one]
  have hprod : (⟨κ, hJ⟩ : J) = ⟨κ * κ₀⁻¹, hδ⟩ * ⟨κ₀, h0⟩ := by
    apply Subtype.ext; simp
  rw [hprod, map_mul, hc, one_mul]

def theta (hP : NG.LevelPara J χ s r ξ) : paraSub s r J χ ξ hP →* ℂˣ where
  toFun := thetaFun hP
  map_one' := by
    have h1 : s.loc n (1 : GAf L n) ∈ paraSub s r J χ ξ hP := by rw [map_one]; exact (paraSub s r J χ ξ hP).one_mem
    have := chi_eq hP 1 (trivOutside_one _) J.one_mem h1
    have e : (⟨s.loc n 1, h1⟩ : paraSub s r J χ ξ hP) = 1 := by apply Subtype.ext; simp
    rw [e] at this
    rw [← this]
    exact map_one χ
  map_mul' := by
    intro g h
    set x := lift s g.1
    set y := lift s h.1
    have hx := lift_mem hP g
    have hy := lift_mem hP h
    have hxy : TrivOutside {s.v} (x * y) :=
      GlobalTheory.SatInd.CosetFin.trivOutside_mul (lift_triv _) (lift_triv _)
    have hm : s.loc n (x * y) ∈ paraSub s r J χ ξ hP := by
      rw [map_mul, loc_lift, loc_lift]; exact (g * h).2
    have := chi_eq hP (x * y) hxy (J.mul_mem hx hy) hm
    have e : (⟨s.loc n (x * y), hm⟩ : paraSub s r J χ ξ hP) = g * h := by
      apply Subtype.ext; simp [x, y, loc_lift]
    rw [e] at this
    rw [← this]
    have e2 : (⟨x * y, J.mul_mem hx hy⟩ : J) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
    rw [e2, map_mul]
    rfl

end main2
end GlobalTheory.ParaLevel

namespace GlobalTheory.ParaLevel

theorem exists_parahoric_char : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L) (r : ℕ) (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (ξ : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ), NG.LevelPara J χ s r ξ → (∃ N : ℕ, ∀ u : (s.v.adicCompletion (maximalRealSubfield L))ˣ, Valued.v ((u : s.v.adicCompletion (maximalRealSubfield L)) - 1) ≤ WithZero.exp (-(N : ℤ)) → ξ u = 1) → ∃ (K : Subgroup (GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)))) (θ : K →* ℂˣ), (∀ g, g ∈ K ↔ NG.ParaRT s r g) ∧ (∀ g (h : g ∈ K) (d : (s.v.adicCompletion (maximalRealSubfield L))ˣ), (d : s.v.adicCompletion (maximalRealSubfield L)) = NG.detDD s r g → θ ⟨g, h⟩ = ξ d) ∧ (∀ g ∈ K, g ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring) ∧ IsOpen (θ.ker : Set K) ∧ ∀ κ, TrivOutside {s.v} κ → ∀ (hJ : κ ∈ J) (h : s.loc n κ ∈ K), χ ⟨κ, hJ⟩ = θ ⟨s.loc n κ, h⟩ := by
  intro L _ _ _ n s r J χ ξ hP hξ
  obtain ⟨N, hN⟩ := hξ
  refine ⟨paraSub s r J χ ξ hP, theta hP, fun g => Iff.rfl, ?_, fun g hg => hg.1, ?_, ?_⟩
  · intro g h d hd
    show χ ⟨lift s g, lift_mem hP ⟨g, h⟩⟩ = ξ d
    exact hP.chr _ _ (lift_triv g) d (by rw [loc_lift]; exact hd)
  · apply Subgroup.isOpen_of_mem_nhds
    have hc : Continuous fun g : paraSub s r J χ ξ hP => NG.detDD s r g.1 :=
      (continuous_detDD s r).comp continuous_subtype_val
    have h1 : NG.detDD s r ((1 : paraSub s r J χ ξ hP) : GL (Fin n) _) = 1 := detDD_one s r
    obtain ⟨π, hπ⟩ := s.v.valuation_exists_uniformizer (maximalRealSubfield L)
    set a : s.v.adicCompletion (maximalRealSubfield L) := ((π : maximalRealSubfield L) : s.v.adicCompletion (maximalRealSubfield L)) ^ N
    have ha : Valued.v a = WithZero.exp (-(N : ℤ)) := by
      simp only [a, map_pow, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ, ← WithZero.exp_nsmul]
      congr 1; simp
    have ha0 : (Valued.v a) ≠ 0 := by rw [ha]; simp
    have hnhds : {x : s.v.adicCompletion (maximalRealSubfield L) |
        Valued.v (x - 1) < WithZero.exp (-(N : ℤ))} ∈ nhds (1 : s.v.adicCompletion (maximalRealSubfield L)) := by
      refine Valued.mem_nhds.2 ⟨Units.mk0 (Valued.v.restrict a) (by rwa [ne_eq, Valuation.restrict_eq_zero_iff]), ?_⟩
      intro y hy
      simp only [Set.mem_setOf_eq, Units.val_mk0] at hy ⊢
      rw [← ha]
      exact (Valuation.restrict_lt_iff _).1 hy
    have hpre := hc.tendsto 1 (by rw [h1]; exact hnhds)
    refine Filter.mem_of_superset hpre ?_
    intro g hg
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hg
    have hne : NG.detDD s r g.1 ≠ 0 := by
      intro h0
      rw [h0, zero_sub, Valuation.map_neg, Valuation.map_one] at hg
      exact absurd hg (not_lt.2 (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega))
    have hθ : theta hP g = ξ (Units.mk0 _ hne) := by
      show χ ⟨lift s g.1, lift_mem hP g⟩ = _
      exact hP.chr _ _ (lift_triv g.1) _ (by rw [loc_lift]; rfl)
    show theta hP g = 1
    rw [hθ]
    exact hN _ (le_of_lt hg)
  · intro κ hκ hJ h
    exact chi_eq hP κ hκ hJ h

end GlobalTheory.ParaLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GeomClausesIff
section
noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite Matrix

namespace GlobalTheory.Et.Rel

variable {X Y : Scheme.{0}} {E : Type} [CommRing E] [TopologicalSpace E] [IsTopologicalRing E]
  {ι : Type} [Fintype ι] [DecidableEq ι] {Γ : Type} [Group Γ]

section
variable (f : X ⟶ Y)

end

variable (E) (f : X ⟶ Y) (Q' : RActPre X Γ) (Q : RActPre Y Γ) (ξ : Γ →* GL ι E)
  (e : ∀ T : Over X, Q'.P.obj (op T) ≃ Q.P.obj (op ((Over.map f).obj T)))
  (he : ∀ {T₁ T₂ : Over X} (v : T₁ ⟶ T₂) (η : Q'.P.obj (op T₂)),
    e T₁ (Q'.P.map v.op η) = Q.P.map ((Over.map f).map v).op (e T₂ η))
  (hq : ∀ (T : Over X) (γ : Γ) (η : Q'.P.obj (op T)), e T ((Q'.act γ).app (op T) η) = (Q.act γ).app _ (e T η))

end GlobalTheory.Et.Rel

namespace GlobalTheory.Et.Rel

variable {X Y : Scheme.{0}} {E : Type} [CommRing E] [TopologicalSpace E] [IsTopologicalRing E]
  {ι : Type} [Fintype ι] [DecidableEq ι] {Γ : Type} [Group Γ]
variable (E) (f : X ⟶ Y) (Q' : RActPre X Γ) (Q : RActPre Y Γ) (ξ : Γ →* GL ι E)
  (e : ∀ T : Over X, Q'.P.obj (op T) ≃ Q.P.obj (op ((Over.map f).obj T)))
  (he : ∀ {T₁ T₂ : Over X} (v : T₁ ⟶ T₂) (η : Q'.P.obj (op T₂)),
    e T₁ (Q'.P.map v.op η) = Q.P.map ((Over.map f).map v).op (e T₂ η))
  (hq : ∀ (T : Over X) (γ : Γ) (η : Q'.P.obj (op T)), e T ((Q'.act γ).app (op T) η) = (Q.act γ).app _ (e T η))

end GlobalTheory.Et.Rel

namespace GlobalTheory.Et.Rel

variable {X Y : Scheme.{0}} {E : Type} [CommRing E] [TopologicalSpace E] [IsTopologicalRing E]
  {ι : Type} [Fintype ι] [DecidableEq ι] {Γ : Type} [Group Γ]
variable (E) (f : X ⟶ Y) (Q' : RActPre X Γ) (Q : RActPre Y Γ) (ξ : Γ →* GL ι E)
  (e : ∀ T : Over X, Q'.P.obj (op T) ≃ Q.P.obj (op ((Over.map f).obj T)))
  (he : ∀ {T₁ T₂ : Over X} (v : T₁ ⟶ T₂) (η : Q'.P.obj (op T₂)),
    e T₁ (Q'.P.map v.op η) = Q.P.map ((Over.map f).map v).op (e T₂ η))
  (hq : ∀ (T : Over X) (γ : Γ) (η : Q'.P.obj (op T)), e T ((Q'.act γ).app (op T) η) = (Q.act γ).app _ (e T η))

end GlobalTheory.Et.Rel

namespace GlobalTheory.UPel.HT

open CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Limits AlgebraicGeometry Opposite Matrix MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
  {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {o' : Obj b N s'} {o : Obj b N s} {f : S' ⟶ S}

def ObjMap.ptEquiv (m : ObjMap o' o f) (T : Over S') : (T ⟶ o'.A) ≃* ((Over.map f).obj T ⟶ o.A) :=
  MulEquiv.ofBijective (pushHom m.cart T) ⟨GlobalTheory.SiegelPull.push_injective m.cart T, GlobalTheory.SiegelPull.push_surjective m.cart T⟩

theorem ObjMap.ptEquiv_left (m : ObjMap o' o f) (T : Over S') (x : T ⟶ o'.A) :
    (m.ptEquiv T x).left = x.left ≫ m.φ := rfl

theorem ObjMap.ptEquiv_act (m : ObjMap o' o f) (T : Over S') (x : T ⟶ o'.A) (c : D.O) :
    m.ptEquiv T (x ≫ o'.act.act c) = m.ptEquiv T x ≫ o.act.act c :=
  Over.OverMorphism.ext (by
    rw [ObjMap.ptEquiv_left, Over.comp_left, Over.comp_left, ObjMap.ptEquiv_left, Category.assoc, m.act,
      Category.assoc])

theorem ObjMap.exists_ptEquiv (m : ObjMap o' o f) (Z : Over S) (g : Z.left ⟶ S') (hg : g ≫ f = Z.hom) :
    ∃ σ : (Over.mk g ⟶ o'.A) ≃* (Z ⟶ o.A), (∀ x, (σ x).left = x.left ≫ m.φ) ∧
      ∀ (n : ℤ) (a c : Over.mk g ⟶ o'.A) (z : Γ(Z.left, ⊤)ˣ),
        (Out.WeilIs o'.A (o'.P.pull (lift (𝟙 o'.A) (𝟙 o'.A)).left) n a c z ↔
          Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n (σ a) (σ c) z) := by
  obtain ⟨Zl, Zr, Zh⟩ := Z
  change Zl ⟶ S' at g
  change g ≫ f = Zh at hg
  subst hg
  refine ⟨m.ptEquiv (Over.mk g), fun x => rfl, fun n a c z => ?_⟩
  exact GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ o.A o'.A f m.φ _ _ (pull_isLB o.isLB _) (pull_isLB o'.isLB _)
    m.cart (GlobalTheory.SiegelPull.diag_iso m.sq m.pol) (Over.mk g) n a c _ _ z rfl rfl

end GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT

open CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Limits AlgebraicGeometry Opposite Matrix MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
  {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {o' : Obj b N s'} {o : Obj b N s} {f : S' ⟶ S}

end GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT

open CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Limits AlgebraicGeometry Opposite Matrix MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
  {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {o' : Obj b N s'} {o : Obj b N s} {f : S' ⟶ S}

end GlobalTheory.UPel.HT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertLongOrbitWordConditionsOfLargeScaleStatement
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertLongOrbitWordConditions_of_large_scale : ∀ eps ez C₂ A : ℝ, 0 < eps → 0 < ez → ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (HW : HWOf D.loc), L.sc.eps = eps → L.sc.ez = ez → Pm.CLw ≤ A → x0 ≤ L.sc.x → LocalSituation.adm7 D → (∀ i, TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i) → LJ.ConclusionJa D → RecS.JointB L HW C₂ := by
  first | exact @GlobalTheory.HTW.RecS.jointB_of_large | exact GlobalTheory.HTW.RecS.jointB_of_large | (intros; apply GlobalTheory.HTW.RecS.jointB_of_large <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPrimeWordConditionsOfLargeScaleStatement
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPrimeWordConditions_of_large_scale : ∀ eps ez A : ℝ, 0 < eps → 0 < ez → ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (HW : HWOf D.loc), L.sc.eps = eps → L.sc.ez = ez → Pm.CLw ≤ A → x0 ≤ L.sc.x → LocalSituation.adm7 D → (∀ i, TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i) → LJ.ConclusionJa D → RecS.JointCD L HW := by
  first | exact @GlobalTheory.HTW.RecS.jointCD_of_large | exact GlobalTheory.HTW.RecS.jointCD_of_large | (intros; apply GlobalTheory.HTW.RecS.jointCD_of_large <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIrreducibleSmoothPullbackPadicRingIsoStatement
section
open GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIrreducibleSmooth_pullback_padic_ringIso : ∀ (g : ℕ) [Fact g.Prime] (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (e : ℚ_[g] ≃+* F), Continuous e → ∀ (n : ℕ) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) F)), IrrSm (Rep.of (σ.ρ.comp (Matrix.GeneralLinearGroup.map e.toRingHom)) : QRep g n) := by
  first | exact @GlobalTheory.SerSys.irrSm_pullback | exact GlobalTheory.SerSys.irrSm_pullback | (intros; apply GlobalTheory.SerSys.irrSm_pullback <;> assumption)
end

