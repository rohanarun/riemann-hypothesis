module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0029
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0027
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ExistsPowMulPredGe
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0028
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SecWbHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HermitianZZEqNeg
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IsClosedSLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ProdIccRange
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.MulVecMapMem
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGram
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PairValPf

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.BruhatHaarProved
section
noncomputable section

namespace Formalism.L2.SG.Pf

theorem jacGauge_of_rhsW (hL : WB.RhsWLim) : JacGauge := jacGauge_of_sandwich_rhsWLim BH.sandwich' hL

end Formalism.L2.SG.Pf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalJacobianOfDoubleCoset
section
namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL

theorem transEx_holds (hHC : HaarCorr) (hW : CoordW) : TransEx := fun hH _ =>
  jacExGood_of_N (jacExGoodN_of_hpkEx_of_pFrame_of_haarCorr hH pFrame_holds hHC zBig bigMem_holds hW secWb_holds)

theorem local_jacobian_of_double_coset (h1 : DiagDCLoc) (hR : RightInvS) (hHC : HaarCorr) (hW : CoordW) : JacLoc :=
  jacLoc_of_ex h1 hR (degRed_holds hR (transEx_holds hHC hW hpkEx_holds hR))

theorem jacLoc_of_rightInv_haarCorr (hR : RightInvS) (hHC : HaarCorr) (hW : CoordW) : JacLoc :=
  local_jacobian_of_double_coset Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.DiagDCLoc_holds hR hHC hW

theorem jacLoc_of_rightInv_setCorr (hR : RightInvS) (hSC : SetCorr) (hW : CoordW) : JacLoc :=
  jacLoc_of_rightInv_haarCorr hR (haarCorr_of hSC) hW

theorem jacLoc_of_setCorr' (hSC : SetCorr) (hW : CoordW) : JacLoc :=
  jacLoc_of_rightInv_setCorr (rightInvS_of hSC (haarCorr_of hSC)) hSC hW

theorem jacLoc_of_setCorr (hSC : SetCorr) : JacLoc :=
  jacLoc_of_setCorr' hSC coordW_holds

theorem jacLoc_holds : JacLoc :=
  jacLoc_of_setCorr setCorr_holds

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGramActRRep
section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
attribute [-instance] PI.WSF.instMeasurableSpaceMat PI.WSF.instBorelSpaceMat
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp Formalism.L2.SG.NormCut

namespace Formalism.L2.SG.Pf.SatGramRep

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Rel

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
  {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem grel_equiv (Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V) : Equivalence (GRel X u u' F0 F0' Λ Λ') := by
  constructor
  · intro p
    exact ⟨1, nlam_one _ _, 1, nlam_one _ _, by simp⟩
  · rintro p q ⟨n, hn, n', hn', h⟩
    exact ⟨n⁻¹, nlam_inv hn, n'⁻¹, nlam_inv hn', by rw [h]; group⟩
  · rintro p q r ⟨n, hn, n', hn', h⟩ ⟨m, hm, m', hm', h'⟩
    exact ⟨m * n, nlam_mul hm hn, n' * m', nlam_mul hn' hm', by rw [h', h]; group⟩

theorem grel_of_mk_eq {Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V} {p q : GCar X u u' F0 F0' Λ Λ'}
    (h : Quot.mk (GRel X u u' F0 F0' Λ Λ') p = Quot.mk _ q) : GRel X u u' F0 F0' Λ Λ' p q :=
  @Quotient.exact _ ⟨GRel X u u' F0 F0' Λ Λ', grel_equiv Λ Λ'⟩ p q h

theorem grel_rep (t : GTerm X u u' F0 F0' what₂ rows') (p : GCar X u u' F0 F0' t.lam t.lam')
    (hp : t.cls = Quot.mk _ p) : GRel X u u' F0 F0' t.lam t.lam' t.rep p :=
  grel_of_mk_eq ((Quot.out_eq t.cls).trans hp)

theorem mem_fam_iff (TR : TypedRed X) (cs : ColSys X u what₂) (cs' : ColSys X u' rows') (FdN FdN' : Set X.B.I.Ginf)
    {t s : GTerm X u u' F0 F0' what₂ rows'} (h : t.toTerm = s.toTerm)
    (S : Set (GTerm X u u' F0 F0' what₂ rows'))
    (hS : S ∈ ({(tOf F0 F0' TR cs cs' FdN FdN').genSet, (tOf F0 F0' TR cs cs' FdN FdN').ngSet,
      (tOf F0 F0' TR cs cs' FdN FdN').degSet} : Set (Set (GTerm X u u' F0 F0' what₂ rows')))) :
    t ∈ S ↔ s ∈ S := by
  have hG : Gt t = Gt s := by
    unfold Gt GTerm.G
    rw [h]
  have hg : t.generic ↔ s.generic := by
    unfold GTerm.generic
    rw [h]
  have hi : t.isId ↔ s.isId := by
    unfold GTerm.isId
    rw [h]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hS
  rcases hS with rfl | rfl | rfl <;>
    simp only [Formalism.FourierDecayAlt.PB.Terms.genSet, Formalism.FourierDecayAlt.PB.Terms.ngSet, Formalism.FourierDecayAlt.PB.Terms.degSet,
      Set.mem_setOf_eq, tOf, hG, hg, hi]

end Rel

section Steps

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}
  {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

variable (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
  (TR : TypedRed X) (cs : ColSys X u what₂) (cs' : ColSys X u' rows')

def IotaRep : Prop :=
  ∀ (Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V), Λ ∈ what₂ → Λ' ∈ rows' → ∀ p q : GCar X u u' F0 F0' Λ Λ',
    GRel X u u' F0 F0' Λ Λ' p q →
      levi TR (kOf X u u' (cs.h (cs.base Λ) : X.B.I.Gf) (cs'.h (cs'.base Λ') : X.B.I.Gf) q.1.1) =
        levi TR (kOf X u u' (cs.h (cs.base Λ) : X.B.I.Gf) (cs'.h (cs'.base Λ') : X.B.I.Gf) p.1.1)

def AmpRepN : Prop :=
  ∀ (Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V), Λ ∈ what₂ → Λ' ∈ rows' → ∀ p q : GCar X u u' F0 F0' Λ Λ',
    GRel X u u' F0 F0' Λ Λ' p q →
    ∀ Ωp Ωq : Set X.B.I.Ginf,
      Formalism.L2.SG.HidaSetting.IsSFund X.B.I (ROset X F0 F0' Λ Λ' p.1.2) Ωp →
      Formalism.L2.SG.HidaSetting.IsSFund X.B.I (ROset X F0 F0' Λ Λ' q.1.2) Ωq →
      OOInt (Formalism.L2.SG.ProjRows.muInf X.B.I) Ωp (X.Wu u) (X.Wu u') p.1.1.1 →
      (haveI := FiniteDimensional.complete ℂ (X.Vpi u)
       chiN X (kOf X u u' (cs.h (cs.base Λ) : X.B.I.Gf) (cs'.h (cs'.base Λ') : X.B.I.Gf) p.1.1) •
          OO (Formalism.L2.SG.ProjRows.muInf X.B.I) Ωp (X.Wu u) (X.Wu u') p.1.1.1 =
        chiN X (kOf X u u' (cs.h (cs.base Λ) : X.B.I.Gf) (cs'.h (cs'.base Λ') : X.B.I.Gf) q.1.1) •
          OO (Formalism.L2.SG.ProjRows.muInf X.B.I) Ωq (X.Wu u) (X.Wu u') q.1.1.1)

variable {F0 F0' TR cs cs'}

theorem iotaOf_of_mk (hI : IotaRep F0 F0' TR cs cs') (t : GTerm X u u' F0 F0' what₂ rows')
    (p : GCar X u u' F0 F0' t.lam t.lam') (hp : t.cls = Quot.mk _ p) :
    iotaOf TR cs cs' t =
      levi TR (kOf X u u' (cs.h (cs.base t.lam) : X.B.I.Gf) (cs'.h (cs'.base t.lam') : X.B.I.Gf) p.1.1) :=
  (hI t.lam t.lam' t.mem t.mem' t.rep p (grel_rep t p hp)).symm

theorem ampN_of_mk (FdN FdN' : Set X.B.I.Ginf) (hA : AmpRepN F0 F0' cs cs')
    (hF : FundExists X u u' F0 F0' what₂ rows') (hO : OOIntAll X u u' F0 F0' what₂ rows')
    (t : GTerm X u u' F0 F0' what₂ rows') (p : GCar X u u' F0 F0' t.lam t.lam') (hp : t.cls = Quot.mk _ p)
    (Ω : Set X.B.I.Ginf) (hΩ : Formalism.L2.SG.HidaSetting.IsSFund X.B.I (ROset X F0 F0' t.lam t.lam' p.1.2) Ω) :
    ampN cs cs' FdN FdN' t =
      (haveI := FiniteDimensional.complete ℂ (X.Vpi u)
       ((scl FdN FdN' (X := X) (u := u) (u' := u') * X.volK2 : ℝ) : ℂ) •
        (chiN X (kOf X u u' (cs.h (cs.base t.lam) : X.B.I.Gf) (cs'.h (cs'.base t.lam') : X.B.I.Gf) p.1.1) •
          OO (Formalism.L2.SG.ProjRows.muInf X.B.I) Ω (X.Wu u) (X.Wu u') p.1.1.1)) := by
  have hFt : Formalism.L2.SG.HidaSetting.IsSFund X.B.I (ROinf t) (FundOf t) := by
    have h := hF t
    unfold FundOf
    rw [dite_eq_left h]
    exact h.choose_spec
  have key := hA t.lam t.lam' t.mem t.mem' t.rep p (grel_rep t p hp) (FundOf t) Ω hFt hΩ (hO t)
  have hc := congrArg (fun z => ((scl FdN FdN' (X := X) (u := u) (u' := u') * X.volK2 : ℝ) : ℂ) • z) key
  exact hc

end Steps

section Closed

open Formalism.L2.SG.Full

def IotaRepC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    IotaRep (what₂ := Y.what₂ u) (rows' := Y.what₂ u') (X.Fu u) (X.Fu u') Y.TR (Y.cs u) (Y.cs u')

def AmpRepNC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    AmpRepN (what₂ := Y.what₂ u) (rows' := Y.what₂ u') (X.Fu u) (X.Fu u') (Y.cs u) (Y.cs u')

end Closed

end Formalism.L2.SG.Pf.SatGramRep
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.UnitriangularPhases
section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.UnitriangularPhases

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.PairVal Formalism.L2.SG.Pf

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

def epsConj (M : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Matrix (Fin (r + 1)) (Fin (r + 1)) E :=
  fun c b => (-1) ^ (r - c.val) * M c b * (-1) ^ (r - b.val)

theorem zhatOM_mul (A Z M : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    ZhatOM (A * Z * M) = A * ZhatOM Z * epsConj M := by
  ext a b
  simp only [ZhatOM, epsConj, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  refine Finset.sum_congr rfl fun d _ => ?_
  have h : ((-1 : E) ^ (r - c.val)) * (-1) ^ (r - c.val) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; simp
  linear_combination (-(A a d * Z d c * M c b * (-1 : E) ^ (r - b.val))) * h

theorem isUpUni_epsConj {M : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (h : IsUpUni M) : IsUpUni (epsConj M) := by
  intro i j
  refine ⟨fun hij => ?_, fun hij => ?_⟩
  · simp only [epsConj]; rw [(h i j).1 hij]; ring
  · subst hij
    simp only [epsConj]
    rw [(h i i).2 rfl, mul_one, ← pow_add, ← two_mul, pow_mul]
    simp

theorem sgUp_epsConj (M : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : sgUp (epsConj M) = -sgUp M := by
  unfold sgUp
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs with h
  · simp only [epsConj]
    have e : r - a.val = (r - (a.val + 1)) + 1 := by omega
    rw [e, pow_succ]
    have hsq : ((-1 : E) ^ (r - (a.val + 1))) * (-1) ^ (r - (a.val + 1)) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; simp
    linear_combination (-(M a ⟨a.val + 1, h⟩)) * hsq
  · simp

theorem isLoUni_conjT {M : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (h : IsUpUni M) : IsLoUni M.conjTranspose := by
  intro i j
  refine ⟨fun hij => ?_, fun hij => ?_⟩
  · rw [Matrix.conjTranspose_apply, (h j i).1 hij, star_zero]
  · subst hij; rw [Matrix.conjTranspose_apply, (h i i).2 rfl, star_one]

theorem sgLo_conjT (M : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : sgLo M.conjTranspose = star (sgUp M) := by
  unfold sgLo sgUp
  rw [star_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs with h
  · rfl
  · simp

theorem zhat_nm (Λ : Submodule (𝓞 E) S.V) {T T' : E} (F : LFlag S r T) (Fs F2 : LFlag S r T')
    {n m : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) (hm : m ∈ NLam Λ Fs) (hF2 : ∀ b, frame F2 b = n (m (frame Fs b))) :
    ∃ vn um : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsUpUni vn ∧ IsUpUni um ∧
      (∀ b, n⁻¹ (frame F b) = ∑ c, vn c b • frame F c) ∧ (∀ b, m (frame Fs b) = ∑ c, um c b • frame Fs c) ∧
      ZhatL F F2 = vn.conjTranspose * ZhatL F Fs * um := by
  have hni := Formalism.L2.SG.Pf.nlam_inv hn
  obtain ⟨vn, hvn, hvnF⟩ := nlam_frame Λ F hni
  obtain ⟨um, hum, humF⟩ := nlam_frame Λ Fs hm
  refine ⟨vn, um, hvn, hum, hvnF, humF, ?_⟩
  ext a b
  have hiso : ∀ x y, S.hT (n⁻¹ x) (n⁻¹ y) = S.hT x y := hni.1.1
  have hnn : ∀ y, n⁻¹ (n y) = y := fun y => by
    rw [← LinearEquiv.mul_apply, inv_mul_cancel]; rfl
  have lhs : ZhatL F F2 a b = S.hT (frame F a) (frame F2 b) := rfl
  rw [lhs, hF2, ← hiso, hnn, hvnF, humF]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ₂, map_smul, Matrix.mul_apply,
    Matrix.conjTranspose_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  simp only [show ∀ x y, ZhatL F Fs x y = S.hT (frame F x) (frame Fs y) from fun _ _ => rfl, starRingEnd_apply,
    RingHom.id_apply]
  ring

theorem phase_move (Λ : Submodule (𝓞 E) S.V) {T T' : E} (F : LFlag S r T) (Fs F2 : LFlag S r T')
    {n m : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) (hm : m ∈ NLam Λ Fs) (hF2 : ∀ b, frame F2 b = n (m (frame Fs b)))
    (w : Point E (r + 1)) {Ls Us L2 U2 : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (hLs : IsLoUni Ls) (hUs : IsUpUni Us)
    (hL2 : IsLoUni L2) (hU2 : IsUpUni U2) (hs : ZhatOM (ZhatL F Fs) = Ls * ptMat w * Us)
    (h2 : ZhatOM (ZhatL F F2) = L2 * ptMat w * U2) :
    ∃ vn um : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsUpUni vn ∧ IsUpUni um ∧
      (∀ b, n⁻¹ (frame F b) = ∑ c, vn c b • frame F c) ∧ (∀ b, m (frame Fs b) = ∑ c, um c b • frame Fs c) ∧
      sgLo L2 + sgUp U2 = sgLo Ls + sgUp Us + star (sgUp vn) - sgUp um := by
  obtain ⟨vn, um, hvn, hum, hvF, humF, hZ⟩ := zhat_nm Λ F Fs F2 hn hm hF2
  refine ⟨vn, um, hvn, hum, hvF, humF, ?_⟩
  have e : (vn.conjTranspose * Ls) * ptMat w * (Us * epsConj um) = L2 * ptMat w * U2 := by
    rw [← h2, hZ, zhatOM_mul, hs]; simp only [Matrix.mul_assoc]
  have hds := simple_decomposition_holds E (r + 1) w _ _ _ _
    (Formalism.MainNotions.BridgeLemma.bru_lo_mul (isLoUni_conjT hvn) hLs) (Formalism.MainNotions.BridgeLemma.bru_up_mul hUs (isUpUni_epsConj hum))
    hL2 hU2 e
  rw [sgLo_mul (isLoUni_conjT hvn) hLs, sgUp_mul hUs (isUpUni_epsConj hum), sgLo_conjT, sgUp_epsConj] at hds
  linear_combination -hds

end Gen

end Formalism.L2.SG.Pf.UnitriangularPhases
end
end

