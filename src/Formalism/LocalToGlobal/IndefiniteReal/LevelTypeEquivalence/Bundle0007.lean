module

public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0006
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0003
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0003
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0005
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0006
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AtTauExUniqueHolds
public import Mathlib

@[expose] public section

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.IterPLin
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def thetaSubO (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) : Submodule ℂ (WO S T → ℂ) where
  carrier := {f | IsThetaFunO ψ S T f}
  zero_mem' := Formalism.IndefR.Fin.theta_zero S T
  add_mem' := fun hf hg => Formalism.IndefR.Fin.theta_add S T hf hg
  smul_mem' := fun c _ hf => Formalism.IndefR.Fin.theta_smul S T c hf

end Formalism.IndefR.Eqv

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.KerDiag
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.Eqv.KerDiag

open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Links.RealDat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Gen

variable {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem dRho_smul (θ : InfFam D) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (c : ℂ)
    (g : WO S T → ℂ) : Datum.dRho (heisO ψ S T) θ τ z (c • g) = c • Datum.dRho (heisO ψ S T) θ τ z g := by
  unfold Formalism.IndefR.Datum.dRho
  funext x
  have hx : ∀ t, heisO ψ S T ((lineAt θ τ z) t) (c • g) x = c * heisO ψ S T ((lineAt θ τ z) t) g x := by
    intro t
    first
      | (rw [map_smul]; rfl)
      | (simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring)
      | (unfold heisO; simp only [Pi.smul_apply, smul_eq_mul]; ring)
      | simp [heisO, mul_left_comm]
  simp only [hx, Pi.smul_apply, smul_eq_mul]
  first
    | exact congrFun (deriv_const_mul_field' c) 0
    | rw [deriv_const_mul_field']
    | done

theorem comm_pureTensorO (hψ : IsStdChar D ψ (-1)) (θ : InfFam D) (hθ : IsInfFam θ)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (W : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ))
    (hW : ∀ τ z g, IsThetaFunO ψ S T g → W (Datum.dRho (heisO ψ S T) θ τ z g) = Datum.dRho (heisO ψ S T) θ τ z (W g))
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (P : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    W (pureTensorO ψ θ S T sS sT BS BT f P) = pureTensorO ψ θ S T sS sT BS BT (W f) P := by
  have hs := Formalism.IndefR.Fin.dRhoStable D ψ θ hψ hθ S T
  have hsub : ∀ u w : WO S T → ℂ, IsThetaFunO ψ S T u → IsThetaFunO ψ S T w →
      IsThetaFunO ψ S T (u - Complex.I • w) := by
    intro u w hu hw
    have h2 := Formalism.IndefR.Fock.CCR.theta_function_linear_combination hu hw 1 (-Complex.I)
    rwa [one_smul, neg_smul, ← sub_eq_add_neg] at h2
  have hsm : ∀ (r : ℂ) (u : WO S T → ℂ), IsThetaFunO ψ S T u → IsThetaFunO ψ S T (r • u) := by
    intro r u hu
    have h2 := Formalism.IndefR.Fock.CCR.theta_function_linear_combination hu hu r 0
    rwa [zero_smul, add_zero] at h2
  have hsmR : ∀ (r : ℝ) (u : WO S T → ℂ), IsThetaFunO ψ S T u → IsThetaFunO ψ S T (r • u) := by
    intro r u hu
    have h2 := hsm (r : ℂ) u hu
    rwa [Complex.coe_smul] at h2
  have hAθ : ∀ x g, IsThetaFunO ψ S T g → IsThetaFunO ψ S T (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT x g) := by
    intro x g hg
    unfold aPlusAll aPlus crea
    first
      | exact hsm _ _ (hsub _ _ (hs _ _ _ hg) (hs _ _ _ hg))
      | exact hsmR _ _ (hsub _ _ (hs _ _ _ hg) (hs _ _ _ hg))
  have hAW : ∀ x g, IsThetaFunO ψ S T g → W (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT x g) = aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT x (W g) := by
    intro x g hg
    unfold aPlusAll aPlus crea
    first
      | rw [map_smul, map_sub, map_smul, hW _ _ _ hg, hW _ _ _ hg]
      | rw [LinearMap.map_smul_of_tower, map_sub, map_smul, hW _ _ _ hg, hW _ _ _ hg]
  unfold Formalism.IndefR.Datum.pureTensorO
  generalize aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT = A at hAθ hAW ⊢
  unfold pureTensorL
  have hL : ∀ L : List (FVar D T.rank S.rank), IsThetaFunO ψ S T (List.foldr (fun i g => A i g) f L) ∧
      W (List.foldr (fun i g => A i g) f L) = List.foldr (fun i g => A i g) (W f) L := by
    intro L
    induction L with
    | nil => exact ⟨hf, rfl⟩
    | cons i L ih =>
      refine ⟨?_, ?_⟩
      · simp only [List.foldr_cons]
        exact hAθ _ _ ih.1
      · simp only [List.foldr_cons]
        rw [hAW _ _ ih.1, ih.2]
  have hO : ∀ m, W (opPow A m f) = opPow A m (W f) := by
    intro m
    unfold opPow
    exact (hL _).2
  first
    | (rw [show (fun m => opPow A m (W f)) = W ∘ (fun m => opPow A m f) from funext fun m => (hO m).symm]
       first
         | (rw [Module.Basis.constr_comp] <;> rfl)
         | (rw [Basis.constr_comp] <;> rfl))
    | (simp only [← hO]
       rw [show (fun m => W (opPow A m f)) = W ∘ (fun m => opPow A m f) from rfl]
       first
         | (rw [Module.Basis.constr_comp] <;> rfl)
         | (rw [Basis.constr_comp] <;> rfl))

theorem pureTensorO_smul (θ : InfFam D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (c : ℂ) (f : WO S T → ℂ) (P : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    pureTensorO ψ θ S T sS sT BS BT (c • f) P = c • pureTensorO ψ θ S T sS sT BS BT f P := by
  have hA : ∀ x (g : WO S T → ℂ), aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT x (c • g) = c • aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT x g := by
    intro x g
    unfold aPlusAll aPlus crea
    rw [dRho_smul, dRho_smul]
    first
      | module
      | rw [smul_comm Complex.I c, ← smul_sub, smul_comm]
      | (simp only [smul_sub, smul_smul]; ring_nf)
  unfold Formalism.IndefR.Datum.pureTensorO
  generalize aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT = A at hA ⊢
  unfold pureTensorL
  have hO : ∀ m, opPow A m (c • f) = c • opPow A m f := by
    intro m
    unfold opPow
    generalize (Finsupp.toMultiset m).toList = L
    induction L with
    | nil => rfl
    | cons i L ih => simp only [List.foldr_cons, ih, hA]
  first
    | rw [show (fun m => opPow A m (c • f)) = c • (fun m => opPow A m f) from funext fun m => hO m,
        map_smul, LinearMap.smul_apply]
    | (simp only [hO]
       rw [show (fun m => c • opPow A m f) = c • (fun m => opPow A m f) from rfl, map_smul, LinearMap.smul_apply])

end Gen

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

end Formalism.IndefR.Eqv.KerDiag

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.MeasBrg
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta
open scoped TensorProduct

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} (fr : UI.Frames D V)

def uM (x : (UI.instV fr).GA) (v : InfinitePlace D.host.F) : Matrix (Fin V.rank) (Fin V.rank) ℂ := uMat (x.1 v)

theorem thetaV_eq_psiT (ρ : D.what₂.Tau) :
    Formalism.L2.SG.AdBridge.thetaV (UI.instV fr) (Formalism.L2.Host.tauPl D ρ) = psiT D ρ := by
  refine RingHom.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | tmul a x =>
    have h1 := Formalism.L2.SG.AdBridge.thetaV_tmul (UI.instV fr) (Formalism.L2.Host.tauPl D ρ) a x
    have h2 : ∀ (a : AF D.host.F) (x : D.host.E),
        psiT D ρ (a ⊗ₜ[D.host.F] x) = gW D (plW D ρ) (fstA D.host.F a) * tauE D ρ x := fun a x => by
      show thetaC D ρ ((fstA D.host.F a) ⊗ₜ[D.host.F] x) = _
      rw [thetaC_tmul]
    refine h1.trans (Eq.trans ?_ (h2 a x).symm)
    have h3 : tauE D ((Formalism.L2.Host.tauPl D).symm (Formalism.L2.Host.tauPl D ρ)) x = tauE D ρ x := by
      rw [Equiv.symm_apply_apply]
    exact congrArg₂ (· * ·) rfl h3
  | add x y hx hy => exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)

theorem P_isUnit_det (v : InfinitePlace D.host.F) : IsUnit (fr.P v).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp (fr.unit v)

theorem infMat_brg (x : (UI.instV fr).GA) (ρ : D.what₂.Tau) :
    infMat D.sp.cm.sig V.gram (thetaC D ρ) (UI.brg fr x) =
      fr.P (Formalism.L2.Host.tauPl D ρ) * uM fr x (Formalism.L2.Host.tauPl D ρ) * (fr.P (Formalism.L2.Host.tauPl D ρ))⁻¹ := by
  have hb : uM fr x (Formalism.L2.Host.tauPl D ρ) = (fr.P (Formalism.L2.Host.tauPl D ρ))⁻¹ *
      (matA D V (UI.brg fr x)).map (psiT D ρ) * fr.P (Formalism.L2.Host.tauPl D ρ) := by
    have h := ((UI.brg_isBridge fr) x).1 (Formalism.L2.Host.tauPl D ρ)
    have h2 := thetaV_eq_psiT fr ρ
    unfold Formalism.L2.SG.AdBridge.ofHAInf at h
    rw [h2] at h
    exact h
  rw [hb, infMat_thetaC]
  have hu := P_isUnit_det fr (Formalism.L2.Host.tauPl D ρ)
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]

theorem mat_eq_one_of_thetaC {M : Matrix (Fin V.rank) (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)}
    (h : ∀ ρ, M.map (thetaC D ρ) = 1) : M = 1 := by
  ext i j
  have hz : M i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)) i j = 0 := by
    apply thetaC_inj
    intro ρ
    have := congrFun (congrFun (h ρ) i) j
    rw [Matrix.map_apply] at this
    rw [map_sub, this, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  exact sub_eq_zero.mp hz

theorem uM_one_iff (x : (UI.instV fr).GA) : x.1 = 1 ↔ ∀ v, uM fr x v = 1 := by
  unfold uM uMat
  constructor
  · rintro h v
    rw [h]
    rfl
  · intro h
    funext v
    exact Subtype.ext (Units.ext (h v))

theorem brg_mem_GfC (x : (UI.instV fr).GA) : UI.brg fr x ∈ GfC V ↔ x.1 = 1 := by
  have key : UI.brg fr x ∈ GfC V ↔ (matA D V (UI.brg fr x)).map (infPart D) = 1 := by
    constructor
    · intro hh
      exact congrArg (fun u : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E) => u.1) (MonoidHom.mem_ker.mp hh)
    · intro hh
      exact MonoidHom.mem_ker.mpr (Units.ext hh)
  rw [key, uM_one_iff]
  have hc : ∀ ρ, ((matA D V (UI.brg fr x)).map (infPart D)).map (thetaC D ρ) =
      fr.P (Formalism.L2.Host.tauPl D ρ) * uM fr x (Formalism.L2.Host.tauPl D ρ) * (fr.P (Formalism.L2.Host.tauPl D ρ))⁻¹ := by
    intro ρ
    rw [← infMat_brg, infMat_thetaC, Matrix.map_map]
    rfl
  constructor
  · intro h1 v
    obtain ⟨ρ, rfl⟩ := (Formalism.L2.Host.tauPl D).surjective v
    have hu := P_isUnit_det fr (Formalism.L2.Host.tauPl D ρ)
    have e' : fr.P (Formalism.L2.Host.tauPl D ρ) * uM fr x (Formalism.L2.Host.tauPl D ρ) * (fr.P (Formalism.L2.Host.tauPl D ρ))⁻¹ = 1 := by
      rw [← hc ρ, h1, Matrix.map_one _ (map_zero _) (map_one _)]
    calc uM fr x (Formalism.L2.Host.tauPl D ρ)
        = (fr.P (Formalism.L2.Host.tauPl D ρ))⁻¹ * (fr.P (Formalism.L2.Host.tauPl D ρ) * uM fr x (Formalism.L2.Host.tauPl D ρ) *
          (fr.P (Formalism.L2.Host.tauPl D ρ))⁻¹) * fr.P (Formalism.L2.Host.tauPl D ρ) := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul, Matrix.mul_assoc,
            Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]
      _ = 1 := by rw [e', Matrix.mul_one, Matrix.nonsing_inv_mul _ hu]
  · intro h1
    apply mat_eq_one_of_thetaC
    intro ρ
    rw [hc ρ, h1, Matrix.mul_one, Matrix.mul_nonsing_inv _ (P_isUnit_det fr _)]

theorem tauF_eq : Formalism.L2.SG.AdBridge.tauF (UI.instV fr) =
    (Lev.swapAE D).comp (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom := by
  refine RingHom.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | tmul a x => exact (Formalism.L2.SG.AdBridge.tauF_tmul (UI.instV fr) a x).trans rfl
  | add x y hx hy => exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)

theorem finE_brg (x : (UI.instV fr).GA) : Lev.finE V (UI.brg fr x) = (x.2.1 : GL (Fin V.rank) (Lev.EAf D)) := by
  apply Units.ext
  have hb := ((UI.brg_isBridge fr) x).2
  unfold Formalism.L2.SG.AdBridge.ofHAFin at hb
  rw [tauF_eq] at hb
  exact hb.symm

end Formalism.IndefR.Eqv

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.MemBlockTriangularTwoBlockSizesOfLe
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.Eqv.Act

open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Links.RealDat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {D : D7} {V : HSp D} {β : GL (Fin V.rank) (EAf D)}

variable {n r : ℕ} {κF : Type} [CommRing κF]

theorem mem_blockTriangular_twoBlockSizes_of_le {r : ℕ} (hn : n ≤ r) (g : GL (Fin n) κF) : g ∈ blockTri (blk2 (n := n) r) := by
  show (g : Matrix (Fin n) (Fin n) κF).BlockTriangular (blk2 r)
  intro i j hij
  have hi : i.val < r := lt_of_lt_of_le i.2 hn
  have hj : j.val < r := lt_of_lt_of_le j.2 hn
  simp [blk2, hi, hj] at hij

theorem block_determinant_empty_eq_one {r : ℕ} (hn : n ≤ r) (g : GL (Fin n) κF) : dBlk (blk2 (n := n) r) 1 g = 1 := by
  unfold dBlk
  rw [extendOne_of_mem _ (mem_blockTriangular_twoBlockSizes_of_le hn g)]
  have : IsEmpty {a : Fin n // blk2 r a = 1} :=
    ⟨fun a => by
      have ha := a.2
      simp [blk2, lt_of_lt_of_le a.1.2 hn] at ha⟩
  ext
  simp [blkDet]

theorem mem_parLev_datY_noQ (hn : V.rank ≤ r) (hr : r ≤ V.rank) (t j : ℕ) (Pg Q : Finset (Pl D.host.E))
    (P : LevelP Pg r ℂ) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ ξ' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (fr : Formalism.IndefR.Lev.Frm)
    (x : GL (Fin V.rank) (EAf D)) :
    x ∈ parLev D.sp.cm V.gram β (datY V.rank r t j hr Pg Q P χ ξ fr) ↔
      x ∈ parLev D.sp.cm V.gram β (datY V.rank r t j hr Pg ∅ P χ ξ' fr) := by
  unfold parLev
  simp only [Subgroup.mem_inf, Subgroup.mem_iInf]
  constructor
  · rintro ⟨h1, -⟩
    refine ⟨h1, fun PP hPP => absurd hPP (Finset.notMem_empty _)⟩
  · rintro ⟨h1, -⟩
    refine ⟨h1, fun PP _ => ?_⟩
    have hst : x ∈ St β := h1.1.2
    exact mem_parah.2 ⟨hst, mem_blockTriangular_twoBlockSizes_of_le (n := V.rank) (κF := kP PP) hn (redFn β PP x)⟩

theorem levFn_datY_noQ (hn : V.rank ≤ r) (hr : r ≤ V.rank) (t j : ℕ) (Pg Q : Finset (Pl D.host.E))
    (P : LevelP Pg r ℂ) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ ξ' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (fr : Formalism.IndefR.Lev.Frm)
    (x : GL (Fin V.rank) (EAf D)) :
    levFn β (flagL (datY V.rank r t j hr Pg Q P χ ξ fr)) x = levFn β (flagL (datY V.rank r t j hr Pg ∅ P χ ξ' fr)) x := by
  unfold levFn
  have hq : ∀ PP ∈ (flagL (datY V.rank r t j hr Pg Q P χ ξ fr)).Q,
      (flagL (datY V.rank r t j hr Pg Q P χ ξ fr)).xq PP
        (dBlk (blk2 (flagL (datY V.rank r t j hr Pg Q P χ ξ fr)).r) 1 (redFn β PP x)) = 1 := by
    intro PP _
    show _ = 1
    rw [show (flagL (datY V.rank r t j hr Pg Q P χ ξ fr)).r = r from rfl, block_determinant_empty_eq_one hn, map_one]
  rw [Finset.prod_eq_one hq]
  rfl

end Gen

section Idem

variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]

end Idem

section GA

variable {D : D7} {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank}

end GA

section MultLev

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

end MultLev

section Real

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem rank_lowerChainSpace_zero_le : (Yc D 0).rank ≤ D.R.r := by
  rw [D.sp.Y_rank _ (min_le_right _ _)]
  show D.R.r + min 0 D.R.m * D.R.t ≤ D.R.r
  simp

end Real

end Formalism.IndefR.Eqv.Act

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ThFEquivOf
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.Eqv.Act

open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Links.RealDat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

def SpanP : Prop :=
  ∀ i, ∀ S ∈ R.Wall i (sg0 D A), (∀ v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, S (fun ρ => v ρ) = 0) → S = 0

end Formalism.IndefR.Eqv.Act

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.TransportedFrame
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField Filter Topology
open scoped TensorProduct ContDiff

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S T : HSp D} {k : ℕ}

end Formalism.IndefR.Eqv

end
end

