module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0196
public import Formalism.LocalToGlobal.Divisibility.RowSideTie
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0870
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0197
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0118
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0017

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftMatrixComputesLiftRational
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.DivisionValues
open Formalism.IndefR.Cx
open scoped InnerProductSpace Matrix

namespace GlobalTheory.Mem.LiftTheta

section Core

variable {K : Type} [Field K] [NumberField K] {σ : K →+* ℂ} {N H : Type} [AddCommGroup N] [Module ℂ N] [AddCommGroup H] [Module ℂ H]

omit [NumberField K] in
theorem semi_expand {d : ℕ} (w : (Fin d → K) →ₛₗ[σ] H) (y : Fin d → K) : w y = ∑ k, σ (y k) • w (Pi.single k 1) := by
  have hz : y = ∑ k, y k • (Pi.single k 1 : Fin d → K) := by
    ext i; simp [Pi.single_apply]
  conv_lhs => rw [hz]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smulₛₗ]

omit [NumberField K] in
theorem semi_injective {d : ℕ} (w : (Fin d → K) →ₛₗ[σ] H) (hli : LinearIndependent ℂ fun k => w (Pi.single k 1)) :
    Function.Injective w := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro y hy
  rw [semi_expand] at hy
  funext k
  exact (map_eq_zero σ).1 (Fintype.linearIndependent_iff.1 hli _ hy k)


theorem oLatTie_of_closure {O : Type} [CommRing O] {φ : O →+* ℂ} (hφ : ∀ a, ∃ b : 𝓞 K, φ a = σ (b : K))
    (M : Rows.OLat O φ N) {d : ℕ} (e : N →ₗ[ℂ] H) (he : Function.Injective e) (j : (Fin d → K) →ₛₗ[σ] N)
    (hj : Function.Injective j) (L : Submodule (𝓞 K) (Fin d → K)) (S : Set H) (hS : ∀ y, y ∈ S ↔ ∃ x ∈ L, e (j x) = y)
    (h : AddSubgroup.closure {y | ∃ a : 𝓞 K, ∃ x ∈ e '' M.carrier, y = σ (a : K) • x} =
      AddSubgroup.closure {y | ∃ a : 𝓞 K, ∃ x ∈ S, y = σ (a : K) • x}) :
    OLatTie σ M j L := by
  classical
  have hR : ∀ y, y ∈ AddSubgroup.closure {y | ∃ a : 𝓞 K, ∃ x ∈ S, y = σ (a : K) • x} ↔ ∃ x ∈ L, e (j x) = y := by
    intro y
    refine ⟨fun hy => ?_, fun hy => AddSubgroup.subset_closure ⟨1, y, (hS y).2 hy, by simp⟩⟩
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, u, hu, rfl⟩ := hy
      obtain ⟨x, hx, rfl⟩ := (hS u).1 hu
      refine ⟨a • x, L.smul_mem a hx, ?_⟩
      rw [← algebraMap_smul K a x, map_smulₛₗ, map_smul]
    | zero => exact ⟨0, L.zero_mem, by simp⟩
    | add _ _ _ _ h1 h2 =>
      obtain ⟨x, hx, rfl⟩ := h1
      obtain ⟨x', hx', rfl⟩ := h2
      exact ⟨x + x', L.add_mem hx hx', by simp⟩
    | neg _ _ h1 =>
      obtain ⟨x, hx, rfl⟩ := h1
      exact ⟨-x, L.neg_mem hx, by simp⟩
  have hgen : ∀ v ∈ M.gen, v ∈ M.carrier := by
    intro v hv
    refine ⟨fun u => if u = v then 1 else 0, ?_⟩
    rw [Finset.sum_eq_single v]
    · simp
    · intro u _ hu
      simp [hu]
    · intro h; exact absurd hv h
  have hL : ∀ y, y ∈ AddSubgroup.closure {y | ∃ a : 𝓞 K, ∃ x ∈ e '' M.carrier, y = σ (a : K) • x} ↔
      ∃ c : N → 𝓞 K, y = e (∑ v ∈ M.gen, σ (c v : K) • v) := by
    intro y
    constructor
    · intro hy
      induction hy using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨a, _, ⟨_, ⟨c, rfl⟩, rfl⟩, rfl⟩ := hy
        choose b hb using hφ
        refine ⟨fun v => a * b (c v), ?_⟩
        rw [← map_smul, Finset.smul_sum]
        simp [hb, mul_smul]
      | zero => exact ⟨0, by simp⟩
      | add _ _ _ _ h1 h2 =>
        obtain ⟨c, rfl⟩ := h1
        obtain ⟨c', rfl⟩ := h2
        refine ⟨c + c', ?_⟩
        rw [← map_add (f := _), ← Finset.sum_add_distrib]
        simp [add_smul]
      | neg _ _ h1 =>
        obtain ⟨c, rfl⟩ := h1
        refine ⟨-c, ?_⟩
        rw [← map_neg, ← Finset.sum_neg_distrib]
        simp
    · rintro ⟨c, rfl⟩
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine AddSubgroup.sum_mem _ fun v hv => AddSubgroup.subset_closure ⟨c v, e v, ⟨v, hgen v hv, rfl⟩, map_smul _ _ _⟩
  refine ⟨fun v hv => ?_, fun x => ⟨fun hx => ?_, ?_⟩⟩
  · have h1 : e v ∈ AddSubgroup.closure {y | ∃ a : 𝓞 K, ∃ x ∈ e '' M.carrier, y = σ (a : K) • x} :=
      AddSubgroup.subset_closure ⟨1, e v, ⟨v, hgen v hv, rfl⟩, by simp⟩
    rw [h, hR] at h1
    obtain ⟨x, -, hx⟩ := h1
    exact ⟨x, he hx⟩
  · have h1 := (hR _).2 ⟨x, hx, rfl⟩
    rw [← h, hL] at h1
    obtain ⟨c, hc⟩ := h1
    exact ⟨c, he hc⟩
  · rintro ⟨c, hc⟩
    have h1 := (hL (e (j x))).2 ⟨c, congrArg e hc⟩
    rw [h, hR] at h1
    obtain ⟨x', hx', hxx⟩ := h1
    rwa [← hj (he hxx)]

omit [NumberField K] in
theorem lin_cpt {d : ℕ} (w : (Fin d → K) →ₛₗ[σ] H) (y : Fin d → K) :
    lin (fun k => w (Pi.single k 1)) (cpt σ y) = w y := (semi_expand w y).symm

end Core

section Lift

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)
  {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (b : Bool)

theorem liftMatrix_computes_lift_rational (h5 : X.H5 cr b) (hr : X.RATth cr b) (j : Bs.J) (t : Bs.Tup) (z : Fin ((lv (fc X.zs) b).dZ j t) → K) :
    X.w0C b j (cpt Bs.v0.embedding (X.liftMat cr b j t *ᵥ z)) = X.θ' j t (X.jL j t (cr.toL X.zs b j t z)) :=
  (X.key_lift cr b h5 hr j t z).trans (lin_cpt (((X.θ' j t).comp (X.jL j t)).comp (cr.toL X.zs b j t)) z)

end Lift

section Main

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

variable (R : RealDat D A Ks) (F : Face D A)

def goodForm (b : Bool) (i : Fin D.R.m) :
    (Fin (Module.finrank D.what₂.LL (R.WL F b i)) → D.what₂.LL) →ₛₗ[D.what₂.embLL] (R.HW i (sg0 D A)).H where
  toFun y := (R.FW i).j (sg0 D A) (∑ k, y k • R.bL F b i k)
  map_add' x y := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, map_add (f := _)]
  map_smul' a y := by
    have h : sg0 D A a = D.what₂.embLL a := by rw [sg0, sgAt_mk _ R.hv0]
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, map_smulₛₗ, h]

theorem goodForm_apply (b : Bool) (i : Fin D.R.m) (y : Fin (Module.finrank D.what₂.LL (R.WL F b i)) → D.what₂.LL) :
    goodForm R F b i y = (R.FW i).j (sg0 D A) (∑ k, y k • R.bL F b i k) := rfl

theorem goodForm_single (b : Bool) (i : Fin D.R.m) (k : Fin (Module.finrank D.what₂.LL (R.WL F b i))) :
    goodForm R F b i (Pi.single k 1) = (R.FW i).j (sg0 D A) (R.bL F b i k) := by
  rw [goodForm_apply]
  congr 1
  simp [Pi.single_apply]

theorem goodForm_li (hU : R.LUnif) (b : Bool) (i : Fin D.R.m) :
    LinearIndependent ℂ fun k => goodForm R F b i (Pi.single k 1) := by
  simp only [goodForm_single]
  exact (hU i _).1 _ _
    ((Module.finBasis D.what₂.LL (R.WL F b i)).linearIndependent.map' (R.WL F b i).subtype (Submodule.ker_subtype _))

theorem sqrt_ne (b : Bool) : ((Real.sqrt (RealDat.nP F b) : ℝ) : ℂ) ≠ 0 := by
  have := Real.sqrt_pos.2 (RealDat.nP_pos (F := F) b)
  exact_mod_cast this.ne'

theorem smul_bC (b : Bool) (i : Fin D.R.m) (k : Fin (Module.finrank D.what₂.LL (R.WL F b i))) :
    ((Real.sqrt (RealDat.nP F b) : ℝ) : ℂ) • R.bC F b i (sg0 D A) k = goodForm R F b i (Pi.single k 1) := by
  rw [goodForm_single, RealDat.bC, smul_smul, Complex.ofReal_inv, mul_inv_cancel₀ (sqrt_ne F b), one_smul]

theorem goodForm_span (b : Bool) (i : Fin D.R.m) :
    Submodule.span ℂ (Set.range fun k => goodForm R F b i (Pi.single k 1)) = R.WS F b i (sg0 D A) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    rw [SetLike.mem_coe]
    beta_reduce
    rw [← smul_bC]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · rw [RealDat.WS, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    rw [SetLike.mem_coe, ← Submodule.smul_mem_iff _ (sqrt_ne F b), smul_bC]
    exact Submodule.subset_span ⟨k, rfl⟩

theorem mem_image_iff (b : Bool) (i : Fin D.R.m) (y : (R.HW i (sg0 D A)).H) :
    y ∈ (R.FW i).j (sg0 D A) '' ((R.FW i).Mj (F.lvl b).P (F.lvl b).ψ⁻¹ (fun g => (idemOf A.X).coeff g) : Set _) ↔
      ∃ x ∈ (R.toCx F).M b i, goodForm R F b i x = y := by
  constructor
  · rintro ⟨f, hf, rfl⟩
    have hW : f ∈ R.WL F b i := (R.FW i).Mj_sub_Wgood _ _ _ hf
    have hs : ∑ k, (Module.finBasis D.what₂.LL (R.WL F b i)).repr ⟨f, hW⟩ k • R.bL F b i k = f := by
      have h := congrArg (R.WL F b i).subtype ((Module.finBasis D.what₂.LL (R.WL F b i)).sum_repr ⟨f, hW⟩)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum] at h
      exact h
    refine ⟨fun k => (Module.finBasis D.what₂.LL (R.WL F b i)).repr ⟨f, hW⟩ k, ((R.FW i).mem_Mcoord _ _ _ _ _).2 ?_, ?_⟩
    · rw [hs]; exact hf
    · exact congrArg ((R.FW i).j (sg0 D A)) hs
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, ((R.FW i).mem_Mcoord _ _ _ _ _).1 hx, rfl⟩

theorem liftWeight_complexPoint_eq_twist (b : Bool) (i : Fin D.R.m) (y : Fin (Module.finrank D.what₂.LL (R.WL F b i)) → D.what₂.LL) :
    (R.toCx F).w0C b i (cpt A.v0.embedding y) = Tw.mk (twAt D.what₂.embLL A.v0) (goodForm R F b i y) := by
  have h1 : (R.toCx F).w0C b i = lin fun k => Tw.semi _ R.emb0 (goodForm R F b i) (Pi.single k 1) := by
    rw [← lin_basis ((R.toCx F).w0C b i)]
    congr 1
    funext k
    exact (congrArg ((R.toCx F).eW b i) (lin_single _ k)).trans (smul_bC R F b i k)
  rw [h1]
  exact lin_cpt (Tw.semi _ R.emb0 (goodForm R F b i)) y

theorem levelFormCoordinateMap_levelZero {s : ℕ} (hOk : A.fam.Ok s) (Zs : DefSub A.fam.amb) (i : Fin D.R.m) (t : T)
    (z : Fin ((A.fam.L i t).dZ (A.fam.lvlA F.P0 F.ψ0) (Zs.Zl i t)) → D.what₂.LL) :
    LiftForms.lvlForm (A.fam.L i t).S (A.fam.L i t).r (A.fam.lvlA F.P0 F.ψ0).P (A.fam.lvlA F.P0 F.ψ0).ψ
      (lZ0 D A F.P0 F.ψ0 Zs i t *ᵥ z) = F.cr.toL Zs false i t z :=
  LiftForms.lvlForm_lE (v0 := A.v0) (s := s) ⟨hOk.conj, hOk.irr, hOk.lifts i t⟩ z


end Main

end GlobalTheory.Mem.LiftTheta

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsSpanOfOnto
section
noncomputable section

open NumberField
open scoped TensorProduct

namespace GlobalTheory.OneMapTuples

open _root_.Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links
  Formalism.IndefR.Mult Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Data

variable {C : Formalism.L2.Pj.Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}
  (O : OMDat C R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1))

def XiConst (ι : (C.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ) (c0 : ℂ) : Prop :=
  ∀ t, GlobalTheory.OneMapAll.CXiAt (Wc D i) (rank_Wc i) (inC O.c') (O.dδ t) (O.U₂ t) (O.dict₂ t) ι x₀ (O.xi t) c0

abbrev IsCls (t : Tp) (x : O.Cl' t → VsV D i O.c'.F) (f : Rul (C.Q.Xo ((i : ℕ) + 1)) O.c') : Prop :=
  IsThClsD (C.Q.Xo ((i : ℕ) + 1)) O.c' (O.dδ t) (O.w t) (O.La t) (O.Nc t) (O.gam t) (O.vol t) (O.ep t) O.io x f

abbrev rdQ (z : G) (f : Rul (C.Q.Xo ((i : ℕ) + 1)) O.c') : AutQ (Wc D i) → ℂ :=
  jFn (Wc D i) (inC O.c') (rdU (unfBC O.hle (C.U ((i : ℕ) + 1)) (inC O.c'))) O.dict O.mu (actLev O.c' O.lev2 z f)

def ClsEx : Prop :=
  ∀ t x, O.Plc t x →
    ∃ f ∈ cusp (C.Q.Xo ((i : ℕ) + 1)) O.c' (unfBC O.hle (C.U ((i : ℕ) + 1))) (wtA κ) (Vc D i).rank, IsCls O t x f ∧
      ∀ f' ∈ sec (C.Q.Xo ((i : ℕ) + 1)) O.c' (wtA κ) (Vc D i).rank, IsCls O t x f' → f' = f

def PtIdent (lam : AutQ (Wc D i) → ℂ) (z : G) (c0 : ℂ) : Prop :=
  ∀ t, ∃ ze : ℂ, ze ∈ D.what₂.embLL.toRatAlgHom.fieldRange ∧ (∃ m : ℕ, 0 < m ∧ ze ^ m = 1) ∧ ∀ x, O.Plc t x →
    ∀ f ∈ sec (C.Q.Xo ((i : ℕ) + 1)) O.c' (wtA κ) (Vc D i).rank, IsCls O t x f →
      ∀ q, c0 * O.thAd t x q = ze * lam q * rdQ O z f q

end Data

abbrev liftQ {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
    (v : (R.MW i (sg0 D A)).Vec) (t : T0) (x : A.fam.amb.FL i t) : AutQ (Wc D i) → ℂ :=
  onQ (Wc D i) (R.thF i t (jVx R i t x) v)

def LiftsSpan {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
    (v : (R.MW i (sg0 D A)).Vec) : Prop :=
  ∀ (t : T0) (x : A.fam.amb.FL i t), liftQ R i v t x ∈ Submodule.span ℂ (Set.range (liftQ R i v A.μ0))

def PinsExist (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
    (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (i : Fin D.R.m) : Prop :=
  QGuard R → ∃ O' : OMDat T.toCore R i T0 id, D.what₂.embLL.toRatAlgHom.fieldRange ≤ O'.c'.F ∧
    O'.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O'.s0)

end GlobalTheory.OneMapTuples
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyFockModelUnitaryDualPair
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta MeasureTheory

namespace GlobalTheory

theorem nonempty_fockData_pair :
    ∀ (p q r s : ℕ) (T0 : GrpData (p * r + q * s) (p * s + q * r)) (T1 : GrpData p q) (T2 : GrpData r s),
      Nonempty (FockData T0 T1 T2) := by
  intro p q r s T0 T1 T2
  obtain ⟨Om, h⟩ := _root_.GlobalTheory.OscGauss.exists_isOsc _ _ T0 (GlobalTheory.Mem.Osc.seqFock _)
  exact GlobalTheory.Osc.nonempty_fockData_iff.2 ⟨h.toOsc⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormSubLeOfDerivIcc
section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum

variable {n : ℕ} {ε : Fin n → Bool}

theorem IsDerFam.hasDerivAt_exp {F : List (Mx n) → Mx n → ℂ} (hF : IsDerFam ε F) {l : List (Mx n)}
    (hl : ∀ Y ∈ l, Y ∈ lieSet ε) {X : Mx n} (hX : X ∈ lieSet ε) {z : Mx n} (hz : z ∈ UJset ε) (s : ℝ) :
    HasDerivAt (fun t : ℝ => F l (z * NormedSpace.exp (t • X))) (F (X :: l) (z * NormedSpace.exp (s • X))) s := by
  have h1 := hF l hl X hX _ (mul_mem_UJ hz (exp_mem_UJ hX s))
  have h2 := HasDerivAt.comp_sub_const s s (by rw [sub_self]; exact h1)
  refine HasDerivAt.congr_of_eventuallyEq h2 (Filter.Eventually.of_forall fun t => ?_)
  show _ = F l (z * _ * _)
  rw [Matrix.mul_assoc, ← exp_add_smul, add_sub_cancel]

theorem norm_sub_le_of_deriv_Icc {f f' : ℝ → ℂ} (hf : ∀ s, HasDerivAt f (f' s) s) {δ B : ℝ} (hδ : 0 ≤ δ)
    (hB : ∀ s ∈ Set.Icc (-δ) δ, ‖f' s‖ ≤ B) {t : ℝ} (ht : t ∈ Set.Icc (-δ) δ) : ‖f t - f 0‖ ≤ B * |t| := by
  have := (convex_Icc (-δ) δ).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s _ => (hf s).hasDerivWithinAt) hB (x := 0) (y := t) ⟨by linarith, hδ⟩ ht
  simpa using this

end GlobalTheory.TypeSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmEqSelfOfLatticeStable
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.Mem.Th GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitHecke

theorem om_eq_self_of_lattice_stable : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (e : AE D), IsSplitIdem D e → ∀ (g : GA D S) (h : GA D T), SuppAt e S g → SuppAt e T h → ∀ x y, IsDetAt e S g x → IsDetAt e T h y → splitFacO χS χT x y = 1 → (∀ u ∈ latO S T (L0c D S) (L0c D T) (fun _ => True), actO S T g⁻¹ h⁻¹ u ∈ latO S T (L0c D S) (L0c D T) (fun _ => True)) → ∀ f, IsThetaFunO ψ S T f → (∀ u ∈ latO S T (L0c D S) (L0c D T) (fun _ => True), IsHalf e u ∨ IsHalf (cA D e) u → heisO ψ S T u f = f) → om (g, h) f = f := by
  intro D ψ S T χS χT om hW e he g h hg hh x y hx hy h1 hL f hf hfix
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hW.std (GlobalTheory.PlaceModel.isSelfDualC_latFrame S)
    (GlobalTheory.PlaceModel.isSelfDualC_latFrame T)).1
  rw [GlobalTheory.PlaceModel.coe_latFrame, GlobalTheory.PlaceModel.coe_latFrame] at hdual
  have hfin := @GlobalTheory.SplitScalar.latO_fin D S T (L0c D S) (L0c D T)
  have key := om_eq_sum hW he hf hfix hg hh hx hy (R := {0})
    (fun u hu => by
      rw [Finset.mem_singleton.1 hu]
      exact ⟨hL 0 (zero_mem _), GlobalTheory.SplitScalar.isHalf_zero e⟩)
    (fun w hw hwe => by
      refine ⟨0, ⟨Finset.mem_singleton_self _, ?_⟩, fun v hv => Finset.mem_singleton.1 hv.1⟩
      rw [sub_zero, hdual w (GlobalTheory.SplitScalar.half_fin he hwe)]
      intro u hu
      rw [← symplO_actO S T g⁻¹ h⁻¹]
      exact (hdual _ (hfin hw)).1 hw _ (hL u hu))
    (fun w hw _ => hL w hw)
  rw [key, h1, Finset.sum_singleton, Finset.card_singleton, GlobalTheory.SplitScalar.heisO_zero]
  simp

end GlobalTheory.SplitHecke
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RetieVolTieGAndCdScaleTie
section
open Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.Mem.Vol GlobalTheory.Mem.Per

namespace GlobalTheory.Mem

theorem retie_volTieG_and_cdScaleTie :
    ∀ D : D7, Formalism.L2.Theta.VolTieG (retie D) ∧ cdScaleTie (retie D) := by
  intro D
  refine ⟨GlobalTheory.T.volumesAgreeAdelic_of_trueVolume (retie D) (fun _ => rfl), ?_⟩
  rw [cdScaleTie_iff]
  exact GlobalTheory.Mem.Vol.ScaleExists.trueScale_isScale D.cd

end GlobalTheory.Mem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SelfDualVectorPairsIntegralFrameColumns
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PairIntegral

theorem sum_mem_intAf {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (Λ : Submodule (𝓞 E) (Fin n → E)) (u : Fin n → E)
    (hu : ∀ y ∈ Λ, ∃ c : 𝓞 E, algebraMap (𝓞 E) E c = ∑ k, u k * y k)
    (z : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) (hz : z ∈ Formalism.L2.Herm.hatL (F := F) Λ) :
    ∑ k, (u k ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) * z k ∈ Formalism.L2.Herm.intAf F E := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨y, hy, rfl⟩ := hz
    obtain ⟨c, hc⟩ := hu y hy
    have hm : (algebraMap (𝓞 E) E c) ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F) ∈ Formalism.L2.Herm.intAf F E :=
      Subring.subset_closure (Or.inl ⟨⟨_, c, rfl⟩, rfl⟩)
    convert hm using 1
    rw [hc, TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun k _ => ?_
    change (u k ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) * (y k ⊗ₜ[F] 1) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  | zero => simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero]; exact zero_mem _
  | add x y _ _ hx hy => simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]; exact add_mem hx hy
  | smul c x _ hx =>
    have := mul_mem c.2 hx
    convert this using 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    change _ * (c.1 * x k) = _
    ring

theorem pair_mem_intAf : ∀ (D : D7) (W : HSp D) (β : GL (Fin W.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)), IsSDFrame W β Λ 1 → ∀ v : Fin W.rank → D.host.E, finVec W v ∈ gLat W 1 → ∀ a : Fin W.rank, ∑ k, eToEAf D (∑ l, D.sp.cm.sig (v l) * W.gram l k) * β.val k a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  intro D W β Λ hβ v hv a
  have hΛ := GlobalTheory.PrincInLevel.eq_latC hβ
  have hfr : Formalism.L2.DIV.IsFrame β Λ := by obtain ⟨c, h, -⟩ := hβ; exact h
  obtain ⟨h1, -, hfg, hsp, -, -, -, -, -, -, hsd⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D W
  have hv' : v ∈ GlobalTheory.Member.latC W := by
    obtain ⟨z, hz, e⟩ := hv
    rw [map_one, Units.val_one, Matrix.one_mulVec] at e
    subst e
    rw [h1] at hz
    exact ((GlobalTheory.AdLat.hat_rational_points_and_approx D.host.F D.host.E W.rank _ hfg hsp).1 v).1 hz
  have hcol : (fun k => β.val k a) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
    refine (hfr _).2 fun i => ?_
    have e : ((β⁻¹).val *ᵥ fun k => β.val k a) i = ((β⁻¹).val * β.val) i a := rfl
    rw [e, Units.inv_mul, Matrix.one_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  refine sum_mem_intAf Λ (fun k => ∑ l, D.sp.cm.sig (v l) * W.gram l k) (fun y hy => ?_) _ hcol
  rw [hΛ] at hy
  obtain ⟨c, hc⟩ := (FractionalIdeal.mem_one_iff _).1 ((hsd y).2 hy v hv')
  refine ⟨c, hc.trans (Finset.sum_congr rfl fun k _ => ?_)⟩
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  change y k * W.gram l k * D.sp.cm.sig (v l) = _
  ring

end GlobalTheory.PairIntegral
end

