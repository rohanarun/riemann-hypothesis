module

public import Mathlib
public import Formalism.SharpRestriction.GrowthBounds.ChartRank.Bundle0001
public import Formalism.SharpRestriction.GrowthBounds.ChartComparison.NrmAMemAdForms
public import Formalism.LocalToGlobal.HermitianColumns.FullSym
public import Formalism.LocalToGlobal.Columns.RecLevelLoc
public import Formalism.LocalRingCardinality.SpanPowerMembership.Places
public import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocGen
public import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocBases
public import Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan.LatSOfLocBasis
public import Formalism.SharpRestriction.GrowthBounds.BaseLevels.LevelsGEmpty
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle0003
public import Formalism.SharpRestriction.GrowthBounds.ChartComparison.Bundle0001
public import Formalism.SharpRestriction.GrowthBounds.ChartComparison.BadQNotOver
public import Formalism.SharpRestriction.GrowthBounds.TwistedLevelAgreement.StepInTwK
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Realises
public import Formalism.LocalToGlobal.InertKernelTheory.StatementAdmAt
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.FrobeniusSqIterateTeichmuller

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DetIntOfLevel
section
noncomputable section

section
namespace GlobalTheory.Port

open _root_.Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.ChartsLv Formalism.MainNotions.G.ChF

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.G.RelativeIndexFlags Formalism.L2.Forms Formalism.L2.Herm Formalism.UG NumberField IsDedekindDomain Matrix
  Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.MainNotions.G.ChartsLv
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}


set_option maxHeartbeats 1000000 in
theorem det_stab_loc (v : HeightOneSpectrum (𝓞 F)) (Lb : Submodule (𝓞 E) (Fin n → E)) (hfg : Lb.FG)
    (hsp : Submodule.span E (Lb : Set (Fin n → E)) = ⊤) (g : GL (Fin n) (E ⊗[F] v.adicCompletion F))
    (hg : g ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v) Lb)) :
    (g : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)).det ∈ intV E v := by
  obtain ⟨q, hq, hv⟩ := Formalism.BasicNotions.Examples₂.PlacesToy.exists_prime_mem v
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨B, hB⟩ := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.exists_isLocBasis q _ Lb hfg hsp
  rw [latS_of_locBasis v hq hv Lb B hB] at hg
  obtain ⟨Bv, hBv⟩ : ∃ Bv, Bv = bc (inclE (F := F) (v.adicCompletion F)) B := ⟨_, rfl⟩
  have hent : ∀ a b, ((Bv⁻¹ * g * Bv : GL (Fin n) (E ⊗[F] v.adicCompletion F)) :
      Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) a b ∈ intV E v := by
    intro a b
    have h1 : (Bv : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ (Pi.single b 1) ∈
        latS (F := F) (v.adicCompletion F) (intV E v) (latB B) := by
      refine (mem_latS_latB v B _).2 fun a' => ?_
      rw [← hBv, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      by_cases h : a' = b
      · subst h
        rw [Pi.single_eq_same]
        exact one_mem _
      · rw [Pi.single_eq_of_ne h]
        exact zero_mem _
    have h3 := (mem_latS_latB v B _).1 ((hg _).1 h1) a
    rw [← hBv, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at h3
    rw [Units.val_mul, Units.val_mul]
    exact h3
  have hd := det_mem_sub (intV E v) _ hent
  have e3 : Matrix.GeneralLinearGroup.det (Bv⁻¹ * g * Bv) = Matrix.GeneralLinearGroup.det g := by
    rw [map_mul, map_mul, map_inv, mul_comm, ← mul_assoc, mul_inv_cancel, one_mul]
  have e4 : ((Bv⁻¹ * g * Bv : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)).det =
      (g : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)).det := congrArg Units.val e3
  rw [← e4]
  exact hd

variable {σ : E →ₐ[F] E} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}


set_option maxHeartbeats 1000000 in
theorem det_int_of_level (S : StepLevel F E σ J T f bad) (x : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (hx : x ∈ S.U) :
    (x : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)).det ∈ intAf F E := by
  refine Formalism.L2.Col.rll_int_of_loc _ fun v => ?_
  have h2 := (S.Uloc_lev v (((S.U_eq x).1 hx).2 v)).2
  have h3 := det_stab_loc v S.Lb (Module.Finite.iff_fg.1 S.Lb_fin) S.Lb_span _ h2
  rw [RingHom.map_det]
  exact h3

theorem det_norm_one (hJ : IsUnit J.det) (x : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (hx : x ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) :
    sigR σ (FiniteAdeleRing (𝓞 F) F) (x : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)).det *
      (x : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)).det = 1 := by
  have h := congrArg Matrix.det (show cT (sigR σ (FiniteAdeleRing (𝓞 F) F)) (x : Matrix (Fin n) (Fin n) _) *
    J.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) * (x : Matrix (Fin n) (Fin n) _) =
      J.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) from hx)
  have hu : IsUnit (J.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F))).det := by
    have e : (J.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F))).det = inclE (F := F) (FiniteAdeleRing (𝓞 F) F) J.det :=
      (RingHom.map_det _ J).symm
    rw [e]
    exact hJ.map _
  rw [Matrix.det_mul, Matrix.det_mul, cT, Matrix.det_transpose] at h
  have e2 : ((x : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)).map (sigR σ (FiniteAdeleRing (𝓞 F) F))).det =
      sigR σ (FiniteAdeleRing (𝓞 F) F) (x : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)).det :=
    (RingHom.map_det _ _).symm
  rw [e2] at h
  refine hu.mul_right_cancel ?_
  rw [one_mul, mul_right_comm]
  exact h

end Gen

variable {D : D7}

theorem scalar_mem_U1Af (d : (D.host.E ⊗[D.host.F] Af D.host.F)ˣ)
    (h : sigR D.sp.cm.sig (Af D.host.F) (d : D.host.E ⊗[D.host.F] Af D.host.F) * d = 1) :
    Matrix.GeneralLinearGroup.scalar (Fin 1) d ∈ unitaryOneFiniteAdeles D.sp.cm := by
  show cT _ _ * _ * _ = _
  ext a b
  fin_cases a; fin_cases b
  simp [cT, Matrix.mul_apply, Matrix.GeneralLinearGroup.scalar, h]

theorem scalar_stab {A : Type} [CommRing A] (R : Subring A) (d : Aˣ) (h1 : (d : A) ∈ R) (h2 : ((d⁻¹ : Aˣ) : A) ∈ R) :
    Matrix.GeneralLinearGroup.scalar (Fin 1) d ∈ stabGL (stdLat (n := Fin 1) (A := A) ↥R) := by
  intro y
  have hmem : ∀ y : Fin 1 → A, y ∈ stdLat (n := Fin 1) (A := A) ↥R ↔ ∀ a, y a ∈ R := by
    intro y
    constructor
    · intro hy a
      obtain ⟨r, hr⟩ := hy a trivial
      rw [← hr]
      exact r.2
    · intro hy a _
      exact ⟨⟨y a, hy a⟩, rfl⟩
  have hsm : ∀ a, ((Matrix.GeneralLinearGroup.scalar (Fin 1) d : GL (Fin 1) A) : Matrix (Fin 1) (Fin 1) A).mulVec y a = d * y a := by
    intro a
    fin_cases a
    simp [Matrix.GeneralLinearGroup.scalar, Matrix.mulVec, dotProduct]
  rw [hmem, hmem]
  constructor
  · intro hy a
    rw [hsm]
    exact mul_mem h1 (hy a)
  · intro hy a
    have h3 := mul_mem h2 (hy a)
    rw [hsm, ← mul_assoc, Units.inv_mul, one_mul] at h3
    exact h3


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem scalar_mem_U1int (d : (D.host.E ⊗[D.host.F] Af D.host.F)ˣ)
    (h : sigR D.sp.cm.sig (Af D.host.F) (d : D.host.E ⊗[D.host.F] Af D.host.F) * d = 1)
    (h1 : (d : D.host.E ⊗[D.host.F] Af D.host.F) ∈ intAf D.host.F D.host.E)
    (h2 : ((d⁻¹ : (D.host.E ⊗[D.host.F] Af D.host.F)ˣ) : D.host.E ⊗[D.host.F] Af D.host.F) ∈ intAf D.host.F D.host.E) :
    Matrix.GeneralLinearGroup.scalar (Fin 1) d ∈ IntegralUnitGroup D.sp.cm :=
  ⟨scalar_mem_U1Af d h, scalar_stab _ d h1 h2⟩


variable (D) in
def detU (i : ℕ) (hi : i ≤ D.R.m) : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) →* unitaryOneFiniteAdeles D.sp.cm :=
  (((Matrix.GeneralLinearGroup.scalar (Fin 1)).comp Matrix.GeneralLinearGroup.det).comp
    (UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)).subtype).codRestrict (unitaryOneFiniteAdeles D.sp.cm)
    fun x => scalar_mem_U1Af _ (det_norm_one (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_gramN_det D i hi) x.1 x.2)

theorem det_detU (i : ℕ) (hi : i ≤ D.R.m) (x : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
    Matrix.GeneralLinearGroup.det (detU D i hi x : GL (Fin 1) (D.host.E ⊗[D.host.F] Af D.host.F)) =
      Matrix.GeneralLinearGroup.det (x : GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by
  show Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 1) _) = _
  rw [Matrix.GeneralLinearGroup.det_scalar]
  simp

variable {i : ℕ} {hi : i ≤ D.R.m} {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}


set_option maxHeartbeats 2000000 in
def detTieOf (H : SymmetricHermitianColumns D) (S : StepLevel D.host.F D.host.E (sigD D) (gramN D i hi) T D.R.f bad) : DetTie S where
  dt := H.dt.comp (detU D i hi)
  dt_rat := by
    intro γ hγ x hx
    have hz : star (γ : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E).det *
        (γ : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E).det = 1 := by
      have h := congrArg Matrix.det (show cT (sigD D : D.host.E →+* D.host.E) γ.1 * gramN D i hi * γ.1 = gramN D i hi from hγ)
      rw [Matrix.det_mul, Matrix.det_mul, cT, Matrix.det_transpose] at h
      have e2 : ((γ : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E).map (sigD D : D.host.E →+* D.host.E)).det =
          (sigD D : D.host.E →+* D.host.E) (γ : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E).det := (RingHom.map_det _ _).symm
      rw [e2] at h
      refine (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_gramN_det D i hi).mul_right_cancel ?_
      rw [one_mul, mul_right_comm]
      exact h
    refine ⟨⟨(γ : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E).det, Unitary.mem_iff.2 ⟨hz, by rw [mul_comm]; exact hz⟩⟩, rfl, ?_⟩
    refine (H.dt_rat _ _ ?_).symm
    rw [det_detU, hx, det_bc]
    exact Units.ext rfl
  dt_U := by
    intro x hx
    rw [H.dt_UO]
    refine ⟨detU D i hi x, Subgroup.mem_subgroupOf.2 ?_, rfl⟩
    refine scalar_mem_U1int _ (det_norm_one (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_gramN_det D i hi) x.1 x.2) (det_int_of_level S x.1 hx) ?_
    rw [← map_inv]
    exact det_int_of_level S x.1⁻¹ (S.U.inv_mem hx)

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Dx cX}

end GlobalTheory.Port

end

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RkLe
section
noncomputable section

namespace GlobalTheory.TwV.DelA

open Formalism.BasicNotions NumberField Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG
open Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)

theorem rkS {j : ℕ} (hN : RankTie X D j) : (X.Pj j).m + 1 = D.R.N j := (rankJ X j).trans hN.1.symm

theorem rkT {j : ℕ} (hN : RankTie X D j) : (X.Pj (j + 1)).m + 1 = D.R.N (j + 1) := (rankJ X (j + 1)).trans hN.2.symm

theorem rk_le {j : ℕ} (hN : RankTie X D j) : D.R.N j ≤ D.R.N (j + 1) := by
  rw [hN.1, hN.2]; exact NN_le X j

def zT {n : ℕ} (f : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (τ : D.what₂.Tau) : Matrix (Fin n) (Fin n) ℂ :=
  if IsOddPos (pos.symm τ).2 then ((f τ)⁻¹).transpose.submatrix id Fin.rev else f τ

def dfr {j : ℕ} (hN : RankTie X D j) (d : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ)
    (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ) (τ : D.what₂.Tau) : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) ℂ :=
  (d τ * f' τ).submatrix id (Fin.castLE (rk_le X D hN))

def evD {Kc : Type} [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) {j : ℕ} (hN : RankTie X D j)
    (d : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ)
    (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ) : DA X Kc j →+* Kc :=
  MvPolynomial.eval₂Hom
    (MvPolynomial.eval fun y : Var (X.Pj (j + 1)) =>
      ι (zT X D pos f' (pos ⟨y.1, y.2.1⟩) (Fin.cast (rkT X D hN) y.2.2.1) (Fin.cast (rkT X D hN) y.2.2.2)))
    (fun z : X.ZA j => ι (d (pos ⟨z.1, z.2.1⟩) (Fin.cast hN.1.symm z.2.2.1) (Fin.cast hN.2.symm z.2.2.2)))

def valZ (i : ℕ) {n : ℕ} (h : (X.Pj i).m + 1 = n) (R : XR (X.Pj i) ℂ) (f : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  MvPolynomial.eval (fun y : Var (X.Pj i) => zT X D pos f (posJ X D pos i ⟨y.1, y.2.1⟩) (Fin.cast h y.2.2.1) (Fin.cast h y.2.2.2)) R

def eT (i : ℕ) (τ : D.what₂.Tau) : ℤ := eAt (X.Pj i) ((posJ X D pos i).symm τ).1 ((posJ X D pos i).symm τ).2

def cT1 (j : ℕ) (τ : D.what₂.Tau) : ℤ := cMu X j (pos.symm τ).1 (pos.symm τ).2

end GlobalTheory.TwV.DelA

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaSeriesDataHypothesesBelowMaximalLevel
section
noncomputable section

namespace GlobalTheory.TwV.Lt

section A

open scoped Matrix
open Formalism.MainNotions.FormalGroupSystem Formalism.L2.KerInert.K1 NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker
open Formalism.L2.G.Pend (Frm)
open Formalism.L2.KerInert.RepFrame (Gm Gp)

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf]
  (M : ∀ j, X.Lt j → ∀ v : X.Pl, Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))
  (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7)
  (large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E))
  (Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))

def FrameLatMapLt (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v) : Prop :=
  ∀ j, j < X.mm → ∀ (L0 : X.Lt j), L0 ∈ Formalism.L2.G.Pend.repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1),
    (X.Pj (j + 1)).IsLatTup La'.2 →
    ∀ (φ : Frm X j L0 La') (r : ℕ) (b : Fin r → Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj j).m + 1)) D.host.E),
      LocBasis D p (YYl D (large₂ j L0 La') (Lg' j L0 La')) b → Orthonormal D b →
      ∀ (i : Fin r) (v : X.Pl),
        (∀ c, ((b i).map (ρ v)).mulVec (fun x => Gm X M φ v x c) ∈ Formalism.MainNotions.G.colSpan (X.G.P.W v) (Gp X M φ v)) ∧
        (∀ c, ((b i).map (fun y => ρ v (D.host.conj y)))ᵀ.mulVec (fun x => Gp X M φ v x c) ∈
          Formalism.MainNotions.G.colSpan (X.G.P.W v) (Gm X M φ v))

end A

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert
open Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ
open Formalism.L2.KerInert.AdmLoc (pendG CurveIn XiIn)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section B

variable {p : ℕ} [Fact p.Prime] {D : D7}

def AdmGLt (X : Sys p) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7) (fd : Formalism.L2.PairingIndexBounds.F.FData X D) : Prop :=
  ∀ j, j < X.mm → ∀ (L0 : X.Lt j), L0 ∈ repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1), (X.Pj (j + 1)).IsLatTup La'.2 →
    TaylorLogMetric.admitted D _ _ (fd.kerN j L0) (fd.kerN (j + 1) La')

def ScalGLt (X : Sys p) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (fd : Formalism.L2.PairingIndexBounds.F.FData X D) (χ : TaylorLogMetric.IdE D → ℂ)
    (muT : ℕ → (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)ˣ → ℂ) (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) : Prop :=
  ∀ j, j < X.mm → ∀ (L0 : X.Lt j), L0 ∈ repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1), (X.Pj (j + 1)).IsLatTup La'.2 →
    Formalism.L2.KerInert.KG.scalG fd χ muT j L0 La' ∈ TaylorLogMetric.Qbar ∧
      ‖(p : ℂ_[p]) ^ Formalism.L2.KerInert.KG.expG X j L0 La' * TaylorLogMetric.lamC lam (Formalism.L2.KerInert.KG.scalG fd χ muT j L0 La')‖ ≤ 1

end B

def XiAwayLt {p : ℕ} [Fact p.Prime] (X : Sys p) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7)
    (Ξ : ∀ j, X.Lt j → X.Lt (j + 1) → Formalism.L2.Col.HomE D.host.E ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ) : Prop :=
  ∃ S₀ : Finset ℕ, p ∉ S₀ ∧ ∀ j, j < X.mm → ∀ (L0 : X.Lt j), L0 ∈ repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1),
    (X.Pj (j + 1)).IsLatTup La'.2 → ∀ y, IntOff S₀ (Ξ j L0 La' y)

section Law

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmb X.G)
  (hfin : ∀ j c, (X.Lv.lev j c).FinClasses)

def StabLawLt (ThR : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) ℂ_[p]) : Prop :=
  letI := wittFractionAlgebraCp p
  letI := algKfC E
  ∀ j < X.mm, ∀ (c : X.Lv.comp j) (L0 : (X.Pj j).Tup) (La' : X.Lt (j + 1)) (ε : (X.Lv.lev j c).Γ),
    (c, L0) ∈ repOf X.Lv hfin j → (X.Pj (j + 1)).IsLatTup La'.2 → (X.Lv.lev j c).smul ε L0 = L0 →
      MvPowerSeries.C ((kapG X ℂ_[p] j c ε)⁻¹) * SA X ℂ_[p] j (gamAt X j c ε) (ThR j (c, L0) La') = ThR j (c, L0) La'

end Law

section Gen

variable {p : ℕ} [Fact p.Prime] {D : D7}

def ThetaSeriesDataHypothesesBelowMaximalLevel (X : Sys p) (E : CEmbC X.G) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses)
    (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (fd : FData X D) (χ : TaylorLogMetric.IdE D → ℂ)
    (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (cl : ℕ)
    (Ξ₀ : ∀ j, X.Lt j → X.Lt (j + 1) → Formalism.L2.Col.HomE D.host.E ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ)
    (muT : ℕ → (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)ˣ → ℂ) : Prop :=
  AdmGLt X hfin D fd ∧ Formalism.L2.KerInert.RepRec.ClAway p cl ∧ XiAwayLt X hfin D Ξ₀ ∧
    ScalGLt X hfin fd χ muT lam ∧
    ∃ ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v,
      Formalism.L2.KerInert.RepFrame.LamPosG X E D pos lam ρ ∧ Formalism.L2.KerInert.RepFrame.MInv X fd.frM ∧
      FrameLatMapLt X fd.frM hfin D (fun j La _ => fd.kerN j La) (fun j _ La' => fd.kerN (j + 1) La') ρ

def LawInLt (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (E : CEmbC X.G)
    {g : GL3Theta.G1 p} (hLT : LTIso g) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)
    (fd : FData X D) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ)
    (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
    (Ξ₀ : ∀ j, X.Lt j → X.Lt (j + 1) → Formalism.L2.Col.HomE D.host.E ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ)
    (muT : ℕ → (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)ˣ → ℂ) : Prop :=
  letI := wittFractionAlgebraCp p
  letI := algKfC E.toCEmb
  StabLawLt X E.toCEmb hfin (thFOf X pos (FrecG E.toCEmb pos fd B χ lam SS cl Ξ₀ muT (ltC g hLT)))

end Gen


open Formalism.L2.KerInert.SecondKernelInstances in
def AdmAtEnt2 : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (Kc0 : G.Consts) (Dx : DivX D)
    (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc0 Dx cX) (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (w : D.what₂.places.Pl) (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) [Fact (D.what₂.places.resChar w).Prime]
    (Fl : Fills (D.gat u w h)) (Lv : Levels Fl) (Ch : Chain Lv) (KA : TwTie.KerAtMu D ex.cmp ex.tw u μ w h Ch)
    (std : _) (vp : _) (unif : _) (eO : _) (eO_spec : _) (dG : _) (dG_spec : _) (om : _)
    [IsFractionRing (sysAt Ch std vp unif eO eO_spec dG dG_spec om).G.O (sysAt Ch std vp unif eO eO_spec dG dG_spec om).G.Kf] (E : CEmbC (sysAt Ch std vp unif eO eO_spec dG dG_spec om).G)
    (hfin : ∀ j c, ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lv.lev j c).FinClasses) (hst : FinStab (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lv)
    (g : GL3Theta.G1 (D.what₂.places.resChar w)) (hLT : LTIso g)
    (pos : (Σ v : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pl, Fin ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).G.P.n' v)) ≃ D.what₂.Tau)
    (Tw : TwForms D) (I : Formalism.MainNotions.G.CmpJ.CmpJIn Tw u μ w h Lv) (L0 : Formalism.L2.PairingIndexBounds.F.Lev0Data D u w h)
    (a : 𝓞 D.host.E) (bad : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ)
    (lam : TaylorLogMetric.Qbar →+* ℂ_[D.what₂.places.resChar w]) (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
    (Ξ₀ : ∀ j, (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt j → (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt (j + 1) →
      Formalism.L2.Col.HomE D.host.E (((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj j).m + 1) (((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj (j + 1)).m + 1) → ℂ)
    (muT : ℕ → (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)ˣ → ℂ),
    CurveIn D (D.what₂.places.resChar w) cc δ g B χ lam →
    ThetaSeriesDataHypothesesBelowMaximalLevel (sysAt Ch std vp unif eO eO_spec dG dG_spec om) E hfin pos (fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad) χ lam cl Ξ₀ muT →
    XiIn (sysAt Ch std vp unif eO eO_spec dG dG_spec om) E hfin hst hLT pos (fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad) B χ lam SS cl Ξ₀ muT →
    LawInLt (sysAt Ch std vp unif eO eO_spec dG dG_spec om) hfin E hLT pos (fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad) B χ lam SS cl Ξ₀ muT →
    (∃ ι Rd Sr, ∀ j < D.R.m,
      TiesAt (Y := pendG (sysAt Ch std vp unif eO eO_spec dG dG_spec om) E hfin hst hLT pos (fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad) B χ lam SS cl Ξ₀ muT) t u μ KA.cls KA.cmp ι Rd Sr j) →
      admitted D (sysAt Ch std vp unif eO eO_spec dG dG_spec om) (pendG (sysAt Ch std vp unif eO eO_spec dG dG_spec om) E hfin hst hLT pos (fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad) B χ lam SS cl Ξ₀ muT)

def CurveEx : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ),
    TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → TaylorLogMetric.IsChi D χ →
    ∀ (p : ℕ) [Fact p.Prime], Nat.Coprime (Ideal.absNorm cc) p → 5 ≤ p → GL3Theta.InertK D p →
    ∀ lam : TaylorLogMetric.Qbar →+* ℂ_[p], ∃ (g : GL3Theta.G1 p) (_ : LTIso g), CurveIn D p cc δ g B χ lam

def dGT (D : D7) (u : D.what₂.Word) (p : ℕ) : ℕ → ℕ := fun j => if j = 0 then 0 else padicValNat p (D.mem u).C.DGam

theorem dGT_zero (D : D7) (u : D.what₂.Word) (p : ℕ) : dGT D u p 0 = 0 := by simp [dGT]

theorem dGT_spec {D : D7} {c : LatCmp D} {Tw : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
    {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} [Fact (D.what₂.places.resChar w).Prime]
    {Fl : Fills (D.gat u w h)} {Lv : Levels Fl} {Ch : Chain Lv} (KA : TwTie.KerAtMu D c Tw u μ w h Ch) :
    ∀ j ≤ Fl.mm, ∀ (a : Lv.comp j) (L : (Fl.Pj j).Tup), (Fl.Pj j).IsLatTup L →
      padicValNat (D.what₂.places.resChar w) (Nat.card {γ : (Lv.lev j a).Γ // (Lv.lev j a).smul γ L = L}) ≤
        dGT D u (D.what₂.places.resChar w) j := by
  intro j hj a L hL
  by_cases h0 : j = 0
  · subst h0
    rw [KA.stab_zero a L hL]
    simp [dGT, Nat.padicValNat_def]
  · have hm : j ≤ D.R.m := by rw [← KA.fl_m]; exact hj
    obtain ⟨_, hdvd⟩ := KA.stab_dvd j hm a L hL
    simp only [dGT, if_neg h0]
    exact ((by simpa only [_root_.Nat.padicValNat_def] using @_root_.multiplicity_dvd_iff_le : ∀ {p : _root_.Nat} [hp : _root_.Fact (_root_.Nat.Prime p)] {a n : _root_.Nat} (ha : a ≠ 0), p ^ n ∣ a ↔ n ≤ _root_.padicValNat p a) (D.mem u).C.DGam_pos.ne').1 (dvd_trans (_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _)) hdvd)

def StdAtW (D : D7) (Gl : G.LatInst D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) : Prop :=
  ∀ v, Std (D.what₂.places.resChar w) ((D.gat u w hg).P.n' v) (D.gat u w hg).P.m (Gl.Fl u w hg).t (Gl.Fl u w hg).mm
    (Gl.Fl u w hg).c (D.gat u w hg).P.r ((Gl.Fl u w hg).TT v) ((Gl.Fl u w hg).a v) ((Gl.Fl u w hg).b v)
    ((D.gat u w hg).P.lam0 v) ((Gl.Fl u w hg).w v)

theorem fracAt {D : D7} (Gl : G.LatInst D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) : IsFractionRing (D.gat u w hg).O (D.gat u w hg).Kf :=
  ((D.gat u w hg).P.setting (Gl.vOf u w hg 0)).frac_O

end GlobalTheory.TwV.Lt

end
end

