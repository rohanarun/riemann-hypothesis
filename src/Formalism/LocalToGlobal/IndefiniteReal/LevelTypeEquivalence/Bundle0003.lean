module

public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0002
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.HfinExistsMat
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.FdomExistsAll
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0013
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
public import Formalism.LocalToGlobal.IndefiniteReal.PHeisFC

@[expose] public section

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory NumberField

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

theorem ga_facts (V : HSp D) :
    IsTopologicalGroup (GA D V) ∧ T2Space (GA D V) ∧ LocallyCompactSpace (GA D V) ∧
      SecondCountableTopology (GA D V) ∧ BorelSpace (GA D V) := by
  obtain ⟨h1, h2, h3⟩ := G5.af_facts D.host.F
  exact G5.ha_facts (AF D.host.F) D.sp.cm.deg2 D.sp.cm.sig V.gram

theorem ae_facts : IsTopologicalRing (AE D) ∧ T2Space (AE D) ∧ LocallyCompactSpace (AE D) ∧
    SecondCountableTopology (AE D) ∧ BorelSpace (AE D) := by
  obtain ⟨h1, h2, h3⟩ := G5.af_facts D.host.F
  exact G5.tens_facts (AF D.host.F) D.sp.cm.deg2

theorem gQDiscrete_holds : GQDiscrete D := fun V => G5.hfin_disc D.sp.cm.sig V.gram

theorem gQ_countable (V : HSp D) : Countable (GQ V) := G5.hfin_countable D.sp.cm.sig V.gram

theorem measurableMul_GA (V : HSp D) : MeasurableMul (GA D V) := by
  obtain ⟨h1, -, -, -, h5⟩ := ga_facts D V
  infer_instance

theorem gfC_secondCountable (V : HSp D) : SecondCountableTopology (GfC V) := by
  obtain ⟨-, -, -, h4, -⟩ := ga_facts D V
  exact Topology.IsInducing.subtypeVal.secondCountableTopology

theorem fundDomExists_holds : FundDomExists D := fun V => by
  obtain ⟨h1, -, -, h4, h5⟩ := ga_facts D V
  have := gQDiscrete_holds D V
  exact G5.fdom_exists_all (GQ V)

end Formalism.IndefR.Eqv

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.IsThetaFunOPull
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField
open scoped TensorProduct ContDiff

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem actO_actO (S T : HSp D) (g g' : GA D S) (h h' : GA D T) (x : WO S T) :
    actO S T g h (actO S T g' h' x) = actO S T (g * g') (h * h') x := by
  unfold actO
  rw [mul_inv_rev, mt_mul, mt_mul]
  simp only [Matrix.mul_assoc]

theorem actO_one (S T : HSp D) (x : WO S T) : actO S T 1 1 x = x := by
  unfold actO
  rw [inv_one, mt_one, mt_one]
  simp

theorem actO_add (S T : HSp D) (g : GA D S) (h : GA D T) (x y : WO S T) :
    actO S T g h (x + y) = actO S T g h x + actO S T g h y := by
  unfold actO
  rw [Matrix.mul_add, Matrix.add_mul]

theorem actO_inv_actO (S T : HSp D) (g : GA D S) (h : GA D T) (x : WO S T) :
    actO S T g h (actO S T g⁻¹ h⁻¹ x) = x := by
  rw [actO_actO, mul_inv_cancel, mul_inv_cancel, actO_one]

theorem actO_actO_inv (S T : HSp D) (g : GA D S) (h : GA D T) (x : WO S T) :
    actO S T g⁻¹ h⁻¹ (actO S T g h x) = x := by
  rw [actO_actO, inv_mul_cancel, inv_mul_cancel, actO_one]

theorem symplO_actO (S T : HSp D) (g : GA D S) (h : GA D T) (x y : WO S T) :
    symplO S T (actO S T g h x) (actO S T g h y) = symplO S T x y := by
  rcases le_or_gt S.rank T.rank with hr | hr
  · obtain ⟨h1, h2⟩ := Brg.bridgeSmall S T hr
    rw [h1, h1, h2, h2, sympl_actHom]
  · obtain ⟨h1, h2⟩ := Brg.bridgeLarge' S T hr
    rw [h1, h1, h2, h2, sympl_actHom]

def pull (S T : HSp D) (g : GA D S) (h : GA D T) : Module.End ℂ (WO S T → ℂ) :=
  LinearMap.funLeft ℂ ℂ (actO S T g h)

theorem mt_GQ (V : HSp D) {γ : GA D V} (hγ : γ ∈ GQ V) :
    ∃ M : Matrix (Fin V.rank) (Fin V.rank) D.host.E, Formalism.L2.Theta.mt V γ = M.map (incA D) := by
  simp only [GQ, HFinIn, HFin, Subgroup.mem_subgroupOf] at hγ
  obtain ⟨u, -, hu⟩ := hγ
  exact ⟨u.1, (congrArg Units.val hu).symm⟩

theorem continuous_actO (S T : HSp D) (g : GA D S) (h : GA D T) : Continuous (actO S T g h) := by
  unfold actO
  exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

end Formalism.IndefR.Eqv

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.RedTheta
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def Red (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {r : ℕ} (C : Matrix (Fin T.rank) (Fin r) D.host.E)
    (μ : Measure (Mx D r S.rank)) (𝓕 : Set (Mx D r S.rank)) (f : WO S T → ℂ) : WO S T → ℂ :=
  fun w => ellI S T C μ 𝓕 (heisO ψ S T w f)

end Formalism.IndefR.Eqv

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.SymplOHSmulRight
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField
open scoped TensorProduct

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S T : HSp D}

theorem eInf_mul_eFin : eInf D * eFin D = 0 := by
  simp only [eInf, eFin, pairA]
  first
  | exact Prod.ext (mul_zero _) (zero_mul _)
  | (refine Prod.ext ?_ ?_ <;> simp)

theorem eInf_add_eFin : eInf D + eFin D = 1 := by
  simp only [eInf, eFin, pairA]
  first
  | exact Prod.ext (add_zero _) (zero_add _)
  | (refine Prod.ext ?_ ?_ <;> simp)

theorem cA_smul (c : AF D.host.F) (z : AE D) : cA D (c • z) = c • cA D z := by

  unfold cA sigR
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [TensorProduct.smul_tmul', Algebra.TensorProduct.map_tmul]
  | add x y hx hy =>
    rw [smul_add, map_add (f := _), map_add (f := _), hx, hy, smul_add]

theorem hO_smul_right (c : AF D.host.F) (x y : WO S T) : hO S T x (c • y) = c • hO S T x y := by

  simp only [hO, Finset.smul_sum, Matrix.smul_apply, Pi.smul_apply, cA_smul, mul_smul_comm, smul_mul_assoc]

theorem hO_smul_left (c : AF D.host.F) (x y : WO S T) : hO S T (c • x) y = c • hO S T x y := by

  simp only [hO, Finset.smul_sum, Matrix.smul_apply, Pi.smul_apply, mul_smul_comm, smul_mul_assoc]

theorem symplOH_smul_right (c : AF D.host.F) (x y : WO S T) : symplOH S T x (c • y) = c * symplOH S T x y := by

  simp only [symplOH, symplO, hO_smul_right, mul_smul_comm, map_smul, smul_eq_mul]
  ring

theorem symplOH_smul_left (c : AF D.host.F) (x y : WO S T) : symplOH S T (c • x) y = c * symplOH S T x y := by

  simp only [symplOH, symplO, hO_smul_left, mul_smul_comm, map_smul, smul_eq_mul]
  ring

theorem symplOH_real_fin (y u : WO S T) (hy : eInf D • y = y) (hu : eFin D • u = u) : symplOH S T y u = 0 := by

  rw [← hy, ← hu, symplOH_smul_left, symplOH_smul_right, ← mul_assoc, eInf_mul_eFin, zero_mul]

theorem wo_real_iff (w : WO S T) : w.map (finPart D) = 0 ↔ eInf D • w = w := by
  constructor
  · intro h
    ext i j
    exact (finPart_eq_zero_iff_smul (w i j)).mp (congrFun (congrFun h i) j)
  · intro h
    ext i j
    exact (finPart_eq_zero_iff_smul (w i j)).mpr (congrFun (congrFun h i) j)

theorem wo_fin_iff (w : WO S T) : w.map (infPart D) = 0 ↔ eFin D • w = w := by
  constructor
  · intro h
    ext i j
    exact (infPart_eq_zero_iff_smul (w i j)).mp (congrFun (congrFun h i) j)
  · intro h
    ext i j
    exact (infPart_eq_zero_iff_smul (w i j)).mpr (congrFun (congrFun h i) j)

end Formalism.IndefR.Eqv

end
end

