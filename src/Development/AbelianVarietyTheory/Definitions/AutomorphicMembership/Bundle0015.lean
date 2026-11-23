module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0208
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanGoodEqMj
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0081

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ClosureImageSpan
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3.MjCoord

theorem closure_image_span {K : Type} [Field K] [NumberField K] {σ : K →+* ℂ} {V H : Type} [AddCommGroup V]
    [Module (𝓞 K) V] [AddCommGroup H] [Module ℂ H] (f : V →+ H) (hfs : ∀ (b : 𝓞 K) (x : V), f (b • x) = σ (b : K) • f x)
    (X : Set V) :
    AddSubgroup.closure {y | ∃ a : 𝓞 K, ∃ x ∈ f '' X, y = σ (a : K) • x} =
      AddSubgroup.closure {y | ∃ a : 𝓞 K, ∃ x ∈ f '' (Submodule.span (𝓞 K) X : Set V), y = σ (a : K) • x} := by
  set C := AddSubgroup.closure {y | ∃ a : 𝓞 K, ∃ x ∈ f '' X, y = σ (a : K) • x}
  have stab : ∀ (b : 𝓞 K), ∀ z ∈ C, σ (b : K) • z ∈ C := by
    intro b z hz
    induction hz using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, x, hx, rfl⟩ := hy
      exact AddSubgroup.subset_closure ⟨b * a, x, hx, by rw [smul_smul, ← map_mul]; norm_cast⟩
    | zero => rw [smul_zero]; exact C.zero_mem
    | add _ _ _ _ h1 h2 => rw [smul_add]; exact C.add_mem h1 h2
    | neg _ _ h1 => rw [smul_neg]; exact C.neg_mem h1
  have key : ∀ x ∈ Submodule.span (𝓞 K) X, f x ∈ C := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact AddSubgroup.subset_closure ⟨1, f x, ⟨x, hx, rfl⟩, by simp⟩
    | zero => rw [map_zero]; exact C.zero_mem
    | add _ _ _ _ h1 h2 => rw [map_add (f := _)]; exact C.add_mem h1 h2
    | smul b x _ h => rw [hfs]; exact stab b _ h
  apply le_antisymm
  · refine AddSubgroup.closure_mono ?_
    rintro _ ⟨a, _, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨a, _, ⟨x, Submodule.subset_span hx, rfl⟩, rfl⟩
  · rw [AddSubgroup.closure_le]
    rintro _ ⟨a, _, ⟨x, hx, rfl⟩, rfl⟩
    rw [← hfs]
    exact key _ (Submodule.smul_mem _ a hx)

theorem majAt_self {K : Type} [Field K] [NumberField K] {n : ℕ} (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ)
    (v : InfinitePlace K) (x : Fin n → K) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v x x =
      ((Formalism.HermitianLatticesTheory.cnorm (Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K (Fin n)) X v x) ^ 2 : ℝ) : ℂ) := by
  rw [Formalism.HermitianLatticesTheory.cnorm, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), Formalism.HermitianLatticesTheory.majAt]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul']

theorem norm_w0C_sq {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A) (b : Bool)
    (hk : X.KForm b) (he : X.EWnorm b) (j : Bs.J) (x : Fin (X.dW b j) → K) :
    ‖X.w0C b j (cpt Bs.v0.embedding x)‖ ^ 2 =
      X.nP b * Formalism.HermitianLatticesTheory.cnorm (Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K _) (X.XW b j) Bs.v0 x) ^ 2 := by
  have h1 := majAt_gram (X.XW b j) Bs.v0 (X.bW b j Bs.v0) (hk j Bs.v0).1 rfl x x
  have h2 := he j (lin (X.bW b j Bs.v0) (cpt Bs.v0.embedding x)) (lin (X.bW b j Bs.v0) (cpt Bs.v0.embedding x))
  rw [← h1, majAt_self, inner_self_eq_norm_sq_to_K] at h2
  have h3 : ((‖X.w0C b j (cpt Bs.v0.embedding x)‖ ^ 2 : ℝ) : ℂ) =
      ((X.nP b * Formalism.HermitianLatticesTheory.cnorm (Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K _) (X.XW b j) Bs.v0 x) ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_mul, ← h2, Complex.ofReal_pow]
    rfl
  exact Complex.ofReal_injective h3

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3}
  {cG : G0 R.Pg D.R.r ≃* G0g D.nd} {X0 : BaseLevelRowSide D} {Y : Read (A3 := A3) R.toRealDat F.lv2 X0}


set_option maxHeartbeats 1000000 in
theorem eW_jW_eq (Z : ReadL R F X0 Y) (i : Fin D.R.m) (y) :
    Y.mj.eW i (Z.jW i y) = GlobalTheory.Mem.LiftTheta.goodForm R.toRealDat F.lv2 false i y :=
  (Z.jW_read i y).trans (congrArg ((R.FW i).j (sg0 D A3.A)) (Fintype.linearCombination_apply _ _ _))

theorem eW_inj (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (i : Fin D.R.m) : Function.Injective (Y.mj.eW i) :=
  GlobalTheory.Mem.LiftForms.inj_of_norm_sq _ (RealDat.nP_pos (F := F.lv2) false) (Y.mj.eW_norm i)

theorem jW_basis (Z : ReadL R F X0 Y) (hH : Holds R F) (i : Fin D.R.m) :
    LinearIndependent ℂ (fun k => Z.jW i (Pi.single k 1)) ∧
      Submodule.span ℂ (Set.range fun k => Z.jW i (Pi.single k 1)) = ⊤ := by
  have he := eW_inj Y i
  have hc : (Y.mj.eW i ∘ fun k => Z.jW i (Pi.single k 1)) = fun k =>
      GlobalTheory.Mem.LiftTheta.goodForm R.toRealDat F.lv2 false i (Pi.single k 1) :=
    funext fun k => eW_jW_eq Z i _
  refine ⟨LinearIndependent.of_comp (Y.mj.eW i) ?_, ?_⟩
  · rw [hc]; exact GlobalTheory.Mem.LiftTheta.goodForm_li R.toRealDat F.lv2 hH.prim.unif false i
  · apply Submodule.map_injective_of_injective he
    rw [Submodule.map_top, Submodule.map_span, ← Set.range_comp, hc]
    exact (GlobalTheory.Mem.LiftTheta.goodForm_span R.toRealDat F.lv2 false i).trans
      ((hH.aux.levelW false i _).trans (Y.mj.eW_range i).symm)

theorem chiKs (hP : Pins R F cG) (i : Fin D.R.m) : (R.FW i).ChiKs := by
  intro g
  have hL := hP.char.base.lev
  have h : ((Formalism.IndefR.FWT.chiC R.toRealDat i g : ℂˣ) : ℂ) ∈ (D.what₂.embLL.comp (algebraMap Ks D.what₂.LL)).fieldRange := by
    unfold Formalism.IndefR.FWT.chiC
    rw [Units.coe_prod]
    refine prod_mem fun PP _ => ?_
    refine GlobalTheory.ChiDetValues.res_mem _ _ _ (hL.mu0 i) (fun x hx => ?_) _ _ (hL.chi i _ PP.2) _
    obtain ⟨y, hy⟩ := hP.keep.valKs i x hx
    exact ⟨y, hy.symm⟩
  obtain ⟨y, hy⟩ := h
  exact ⟨y, D.what₂.embLL.injective (hy.trans ((Units.coe_prod _ _).trans (hP.char.base.grp.chiW i g).symm))⟩


set_option maxHeartbeats 1000000 in
theorem jW_lat (Z : ReadL R F X0 Y) (hP : Pins R F cG) (hH : Holds R F) (i : Fin D.R.m) :
    OLatTie D.what₂.embLL (D.what₂.MjLat ((i : ℕ) + 1)) (Z.jW i) ((s0Of R F).M i) := by
  have he := eW_inj Y i
  have hli := (jW_basis Z hH i).1
  have hej := eW_jW_eq Z i
  have hI := hH.aux.integral i
  have hspan := GlobalTheory.GoodLatDescent.span_MK_good (R.FW i) hI.1 (fun g f => (hI.2.2 g f).1)
    (chiKs hP i) F.P0 F.ψ0⁻¹ (fun g => (idemOf A3.A.X).coeff g)
    (fun p => ?_) hP.keep.levKs.2
  swap
  · obtain ⟨y, hy⟩ := hP.keep.levKs.1 p
    exact ⟨y⁻¹, by rw [map_inv₀, hy, MonoidHom.inv_apply, Units.val_inv_eq_inv_val]; rfl⟩
  have hsg : sg0 D A3.A = D.what₂.embLL := RingHom.ext fun a => by rw [sg0, sgAt_mk _ R.hv0]
  have himg : Y.mj.eW i '' (D.what₂.MjLat ((i : ℕ) + 1)).carrier =
      (R.FW i).j (sg0 D A3.A) '' {y | y ∈ (R.FW i).MK ∧ y ∈ (R.FW i).Wgood F.P0 F.ψ0⁻¹ (fun g => (idemOf A3.A.X).coeff g)} := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨y, hy1, hy2, e⟩ := (Y.mj.eW_lat i x).1 hx
      exact ⟨y, ⟨hy1, hy2⟩, e.symm⟩
    · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
      have hyM : y ∈ (R.FW i).Mj F.P0 F.ψ0⁻¹ (fun g => (idemOf A3.A.X).coeff g) := by
        rw [← hspan]; exact Submodule.subset_span ⟨hy1, hy2⟩
      obtain ⟨c, -, hcy⟩ := (GlobalTheory.Mem.LiftTheta.mem_image_iff R.toRealDat F.lv2 false i _).1 ⟨y, hyM, rfl⟩
      exact ⟨Z.jW i c, (Y.mj.eW_lat i _).2 ⟨y, hy1, hy2, (hej c).trans hcy⟩, (hej c).trans hcy⟩
  refine GlobalTheory.Mem.LiftTheta.oLatTie_of_closure (fun a => ⟨⟨D.what₂.OtoLL a, D.O_int a⟩, rfl⟩) _ (Y.mj.eW i) he (Z.jW i)
    (GlobalTheory.Mem.LiftTheta.semi_injective _ hli) _
    ((R.FW i).j (sg0 D A3.A) '' ((R.FW i).Mj F.P0 F.ψ0⁻¹ (fun g => (idemOf A3.A.X).coeff g) : Set _)) (fun y => ?_) ?_
  · refine (GlobalTheory.Mem.LiftTheta.mem_image_iff R.toRealDat F.lv2 false i y).trans ?_
    exact ⟨fun ⟨x, hx, h⟩ => ⟨x, hx, (hej x).trans h⟩, fun ⟨x, hx, h⟩ => ⟨x, hx, (hej x).symm.trans h⟩⟩
  · rw [himg, ← hspan]
    exact closure_image_span (σ := D.what₂.embLL) ((R.FW i).j (sg0 D A3.A)).toAddMonoidHom
      (fun b x => by
        rw [← hsg]
        show (R.FW i).j _ (b • x) = _
        rw [← algebraMap_smul D.what₂.LL b x, map_smulₛₗ]
        rfl) _


set_option maxHeartbeats 1000000 in
theorem jW_norm (Z : ReadL R F X0 Y) (hH : Holds R F) (i : Fin D.R.m) (x : Fin ((s0Of R F).dW i) → D.what₂.LL) :
    Formalism.HermitianLatticesTheory.cnorm (Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun D.what₂.LL _) ((s0Of R F).XW i) (InfinitePlace.mk D.what₂.embLL) x) =
      ‖Z.jW i x‖ := by
  have h1 := norm_w0C_sq (R.toCx3 F) false (RealDat3.kForm_of hH.prim.unif false) (RealDat3.ewNorm false) i x
  have h2 : (R.toCx3 F).w0C false i (cpt A3.A.v0.embedding x) =
      Tw.mk (twAt D.what₂.embLL A3.A.v0) (GlobalTheory.Mem.LiftTheta.goodForm R.toRealDat F.lv2 false i x) :=
    GlobalTheory.Mem.LiftTheta.liftWeight_complexPoint_eq_twist R.toRealDat F.lv2 false i x
  have h3 : ‖(R.toCx3 F).w0C false i (cpt A3.A.v0.embedding x)‖ = ‖Y.mj.eW i (Z.jW i x)‖ :=
    (congrArg norm h2).trans (congrArg norm (eW_jW_eq Z i x)).symm
  have h4 := Y.mj.eW_norm i (Z.jW i x)
  have h5 : RealDat.nP F.lv2 false *
      Formalism.HermitianLatticesTheory.cnorm (Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun D.what₂.LL _) ((s0Of R F).XW i) A3.A.v0 x) ^ 2 =
        RealDat.nP F.lv2 false * ‖Z.jW i x‖ ^ 2 := by
    rw [← h4, ← h3]
    exact h1.symm
  rw [← R.hv0]
  exact (sq_eq_sq₀ (Real.sqrt_nonneg _) (norm_nonneg _)).1
    (mul_left_cancel₀ (RealDat.nP_pos (F := F.lv2) false).ne' h5)

end GlobalTheory.Mem.R3.MjCoord

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
section
noncomputable section

namespace GlobalTheory.Mem.SRe

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV
  Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  MeasureTheory NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G' : Type} [Group G'] [Fintype G'] {Pl0 T : Type} {A : FamIn D.what₂.LL G' Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

abbrev JR (R : RealDat D A Ks) (F : Face D A) : Set (GA D (Yc D 0)) := levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))

abbrev chiR (R : RealDat D A Ks) (F : Face D A) : GA D (Yc D 0) → ℂ := levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))

abbrev MultR (R : RealDat D A Ks) (F : Face D A) : Submodule ℂ (MMap (MP R)) := Mult R.θ (R.MY 0) (JR R F) (chiR R F)

def DallTie (R : RealDat D A Ks) (F : Face D A) : Prop := D.what₂.Dall = Module.finrank ℂ (MultR R F)

def concreteLevelAdelicSubset (X : HidaSetting D) : Set X.B.I.GA := {x | x.1 = 1 ∧ x.2 ∈ X.K2}

def adelicCharacterOfHidaSetting (X : HidaSetting D) : X.B.I.GA → ℂ := fun x => star (X.chi2 x.2)

def GrpPin (R : RealDat D A Ks) : Prop :=
  ∃ (eR : G' ≃* G0g D.nd) (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg)
      (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1),
    (∀ kv, ((plg kv : R.Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) ∧
    (∀ g, D.what₂.embLL ((idemOf A.X).coeff g) = D.ntypes.e0.coeff (eR g)) ∧ (∀ kv, R.C.P.Div kv.1 (plg kv).1) ∧
      ∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) (eR g kv)

structure SeeAt (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (t : GA D (D.sp.Y 0)) : Prop where

  fin : t ∈ GfC (Yc D 0)

  conj : ConjLevel t⁻¹ (JR R F) (chiR R F) (iotaX X h ⁻¹' concreteLevelAdelicSubset X) (fun k => adelicCharacterOfHidaSetting X (iotaX X h k))

  mat : RowLevelMatchAt R F X h t

def conjRows (X : HidaSetting D) : Submodule ℂ (L2X X) := (HHX X).comap (conjL (muX X)).toLinearEquiv.toLinearMap

def EvalOn (R : RealDat D A Ks) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0))
    (v₀ : (MP R).Vec) (c : ℝ) (E : Submodule ℂ (MMap (MP R))) (E' : Submodule ℂ (L2X X)) : Prop :=
  ∃ J : E ≃ₗ[ℂ] E', ∀ S : E,
    ((J S : E') : L2X X) =ᵐ[muX X] (fun x => ev (MP R) v₀ (S : MMap (MP R)) ((iotaX X h).symm x * t)) ∧
      ‖((J S : E') : L2X X)‖ ^ 2 = c * (ipM (MP R) R.ν0 R.fd0 (S : MMap (MP R)) (S : MMap (MP R))).re

def RowJ (R : RealDat D A Ks) (eE : D.what₂.EE →ₗ[ℂ] R.HE.H) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (G : GoodOp X) (t : GA D (D.sp.Y 0)) (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC X G) : Prop :=
  ∃ v₀ : (MP R).Vec, (∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1) ∧ ∃ a : ℝ, 0 < a ∧ ∀ x : D.what₂.EE,
    ((j x : EEC X G) : L2X X) =ᵐ[muX X] fun g => (a : ℂ) * ev (MP R) v₀ (R.HE.e (eE x)) ((iotaX X h).symm g * t)

theorem SeeAt.levelMatchA {R : RealDat D A Ks} {F : Face D A} {X : HidaSetting D}
    {h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D} {t : GA D (D.sp.Y 0)} (hs : SeeAt R F X h t) : LevelMatchA R F X h t := by
  intro k hk
  have e : (t⁻¹⁻¹ * (t⁻¹ * (iotaX X h).symm (1, k) * t) * t⁻¹ : GA D (D.sp.Y 0)) = (iotaX X h).symm (1, k) := by group
  obtain ⟨h1, h2⟩ := hs.conj (t⁻¹ * (iotaX X h).symm (1, k) * t)
  rw [e] at h1 h2
  have hm := h1.2 (by simp [concreteLevelAdelicSubset, hk])
  refine ⟨hm, ?_⟩
  have := h2 hm
  simp only [adelicCharacterOfHidaSetting, ContinuousMulEquiv.apply_symm_apply] at this
  exact this.symm

theorem exists_rowJ_of_evalOn {R : RealDat D A Ks} {F : Face D A} {X : HidaSetting D}
    {h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D} {G : GoodOp X} {t : GA D (D.sp.Y 0)} {v₀ : (MP R).Vec} {c : ℝ}
    {eE : D.what₂.EE →ₗ[ℂ] R.HE.H} (hc : 0 < c) (hv₀ : ∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1) (hE : R.models_HE)
    (hrange : LinearMap.range eE = (R.EEat (R.levR F true)).comap R.HE.e)
    (hnorm : ∀ x, ‖eE x‖ ^ 2 = RealDat.nP F true * ‖x‖ ^ 2) (hle : R.EEat (R.levR F true) ≤ R.EEat R.triv)
    (hJ2 : EvalOn R X h t v₀ c (EP R F) (EEC X G)) : ∃ j : D.what₂.EE ≃ₗᵢ[ℂ] EEC X G, RowJ R eE X h G t j := by
  obtain ⟨J2, hJ2⟩ := hJ2
  obtain ⟨he_inj, he_range, he_ip⟩ := hE
  have hnP : 0 < RealDat.nP F true := by
    unfold RealDat.nP
    exact_mod_cast Nat.card_pos
  have heE_inj : Function.Injective eE := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h1 := hnorm x
    rw [hx, norm_zero] at h1
    have h2 : RealDat.nP F true * ‖x‖ ^ 2 = 0 := by rw [← h1]; ring
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 hnP.ne'
    · exact norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h3)
  have hmem : ∀ x, (R.HE.e ∘ₗ eE) x ∈ EP R F := fun x => by
    have : eE x ∈ (R.EEat (R.levR F true)).comap R.HE.e := hrange ▸ LinearMap.mem_range_self eE x
    exact this
  let k : D.what₂.EE →ₗ[ℂ] EP R F := LinearMap.codRestrict (EP R F) (R.HE.e ∘ₗ eE) hmem
  have hk : Function.Bijective k := by
    constructor
    · intro x y hxy
      exact heE_inj (he_inj (congrArg Subtype.val hxy))
    · rintro ⟨y, hy⟩
      have hy' : y ∈ LinearMap.range R.HE.e := he_range ▸ hle hy
      obtain ⟨z, rfl⟩ := hy'
      have hz : z ∈ LinearMap.range eE := by rw [hrange]; exact hy
      obtain ⟨x, rfl⟩ := hz
      exact ⟨x, rfl⟩
  let L : D.what₂.EE ≃ₗ[ℂ] EEC X G := (LinearEquiv.ofBijective k hk).trans J2
  have hLn : ∀ x, ‖L x‖ ^ 2 = (c * RealDat.nP F true) * ‖x‖ ^ 2 := by
    intro x
    have h1 := (hJ2 (k x)).2
    have h2 : ((k x : EP R F) : MMap (MP R)) = R.HE.e (eE x) := rfl
    have h3 : (ipM (MP R) R.ν0 R.fd0 (R.HE.e (eE x)) (R.HE.e (eE x))).re = ‖eE x‖ ^ 2 := by
      calc (ipM (MP R) R.ν0 R.fd0 (R.HE.e (eE x)) (R.HE.e (eE x))).re
          = (inner ℂ (eE x) (eE x)).re := by rw [he_ip]; rfl
        _ = ‖eE x‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) (eE x)
    show ‖((J2 (k x) : EEC X G) : L2X X)‖ ^ 2 = _
    rw [h1, h2, h3, hnorm x]
    ring
  set a : ℝ := (Real.sqrt (c * RealDat.nP F true))⁻¹ with ha_def
  have hs : 0 < Real.sqrt (c * RealDat.nP F true) := Real.sqrt_pos.mpr (mul_pos hc hnP)
  have ha : 0 < a := inv_pos.mpr hs
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  let j : D.what₂.EE ≃ₗᵢ[ℂ] EEC X G :=
    { toLinearEquiv := L.trans (LinearEquiv.smulOfNeZero ℂ (EEC X G) (a : ℂ) haC)
      norm_map' := fun x => by
        show ‖(a : ℂ) • L x‖ = ‖x‖
        have hL : ‖L x‖ = Real.sqrt (c * RealDat.nP F true) * ‖x‖ := by
          rw [← Real.sqrt_sq (norm_nonneg (L x)), hLn x, Real.sqrt_mul' _ (sq_nonneg _),
            Real.sqrt_sq (norm_nonneg x)]
        rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg ha.le, hL, ← mul_assoc, ha_def,
          inv_mul_cancel₀ hs.ne', one_mul] }
  refine ⟨j, v₀, hv₀, a, ha, fun x => ?_⟩
  have h1 : ((j x : EEC X G) : L2X X) = (a : ℂ) • ((J2 (k x) : EEC X G) : L2X X) := rfl
  rw [h1]
  filter_upwards [Lp.coeFn_smul (a : ℂ) ((J2 (k x) : EEC X G) : L2X X), (hJ2 (k x)).1] with g h2 h3
  rw [h2, Pi.smul_apply, h3, smul_eq_mul]
  rfl

end GlobalTheory.Mem.SRe

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GeoExV
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.R3

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}

def GeoExV (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (C : Formalism.L2.Pj.CoreJ D) [Algebra C.Q.c.F D.what₂.LL]
    (F : Face D A3.A) : Prop :=
  ∀ (R : RealDat D A3.A C.Q.c.F) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Formalism.L2.Host.ValLL D R.C → GlobalTheory.RealGeo.PreChar R → R.grp_levels F → C.pb = R.C.P.pb →
    Keep (A3 := A3) R F cG → ∃ dict mu chiW x₀ cE nW FW,
      (R.upd5 nW FW R.mu R.twPl R.err0).grp_chiW ∧
      Nonempty (@GlobalTheory.RealGeo.GeoHalf D G _ _ Pl0 T A3.A (GlobalTheory.RealGeo.reCore C dict mu chiW x₀ cE)
        (inferInstanceAs (Algebra C.Q.c.F D.what₂.LL)) (R.upd5 nW FW R.mu R.twPl R.err0) fun _ => 1) ∧
      ∀ i x, ∃ y, (FW i).j (sg0 D A3.A) y = R.thG i A3.A.μ0 (R.jV i A3.A.μ0 x)

end GlobalTheory.Mem.R3
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
section
noncomputable section

namespace GlobalTheory.Mem.Col2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (JetsRatDeg)

section Deg

variable {T : Type} {a b : ℕ}


open Classical in
def monoDeg (e : DVar T a b →₀ ℕ) (τ : T) : ℕ := ∑ k ∈ e.support.filter (fun k => k.1 = τ), e k

theorem monoDeg_eq_sum [Fintype T] (e : DVar T a b →₀ ℕ) (τ : T) : monoDeg e τ = ∑ β, ∑ α, e (τ, β, α) := by
  unfold monoDeg
  rw [Finset.sum_filter, Finset.sum_subset (Finset.subset_univ e.support) (fun k _ hk => by
    simp only [Finsupp.mem_support_iff, not_not] at hk
    simp [hk])]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single τ]
  · simp [Fintype.sum_prod_type]
  · intro t _ ht
    simp [ht]
  · intro h
    exact absurd (Finset.mem_univ τ) h

theorem exists_monoDeg [Fintype T] (ha : 0 < a) (hb : 0 < b) (n : T → ℕ) : ∃ e : DVar T a b →₀ ℕ, ∀ τ, monoDeg e τ = n τ := by
  classical
  refine ⟨∑ t, Finsupp.single (t, (⟨0, hb⟩ : Fin b), (⟨0, ha⟩ : Fin a)) (n t), fun τ => ?_⟩
  rw [monoDeg_eq_sum, Finset.sum_eq_single (⟨0, hb⟩ : Fin b)]
  · rw [Finset.sum_eq_single (⟨0, ha⟩ : Fin a)]
    · simp [Finsupp.finsetSum_apply, Finsupp.single_apply]
    · intro α _ hα
      simp [Finsupp.finsetSum_apply, Ne.symm hα]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro β _ hβ
    refine Finset.sum_eq_zero fun α _ => ?_
    simp [Finsupp.finsetSum_apply, Ne.symm hβ]
  · intro h
    exact absurd (Finset.mem_univ _) h

end Deg

namespace ColIn

variable {B : Base} {X : PreX B.toPre} (I : ColIn B X)

abbrev Sb (a : I.ι) (u : B.Word) : Finset (HeightOneSpectrum (𝓞 B.fields.E)) :=
  Sall (Pr := B.primes X) I.sel (I.tup a) u

abbrev modulus (a : I.ι) (u : B.Word) : ℕ :=
  cAof (Pr := B.primes X) I.sel (I.tup a) (I.cst a) * cBof (Pr := B.primes X) I.sel (I.tup a) (I.cst a) u

end ColIn

abbrev nuDeg (B : Base) (u : B.Word) (i : ℕ) (τ : B.fields.Tau) : ℤ := ∑ r, (B.wts.nuW u (i + 1) τ).w r

theorem nuDeg_nonneg (B : Base) (u : B.Word) {i : ℕ} (hi : i < B.R.m) (τ : B.fields.Tau) : 0 ≤ nuDeg B u i τ := by
  have h0 := GlobalTheory.MoveCompare.nuW_detShift_nonneg B.wts u hi τ
  unfold nuDeg
  refine Finset.sum_nonneg fun r _ => le_trans h0 ?_
  unfold DomWeight.detShift
  split_ifs with h
  · apply DomWeight.anti
    rw [Fin.le_iff_val_le_val]
    have := r.isLt
    simp only
    omega
  · exact absurd (lt_of_le_of_lt (Nat.zero_le _) r.isLt) h

theorem exists_monoDeg_nuDeg (B : Base) (u : B.Word) {i : ℕ} (hi : i < B.R.m) :
    ∃ e : DVar B.fields.Tau (B.R.N i) (B.R.N (i + 1)) →₀ ℕ, ∀ τ, (monoDeg e τ : ℤ) = nuDeg B u i τ := by
  have hk := B.R.m_add_three_le_k
  have h1 : 0 < B.R.N i := by
    show 0 < B.R.k + i * (B.R.t + 1)
    omega
  have h2 : 0 < B.R.N (i + 1) := by
    show 0 < B.R.k + (i + 1) * (B.R.t + 1)
    omega
  obtain ⟨e, he⟩ := exists_monoDeg (T := B.fields.Tau) h1 h2 (fun τ => (nuDeg B u i τ).toNat)
  exact ⟨e, fun τ => by rw [he τ]; exact Int.toNat_of_nonneg (nuDeg_nonneg B u hi τ)⟩

private theorem monoDeg_eq_sum_filter {T : Type} {a b : ℕ} {d : DecidableEq T} (e : DVar T a b →₀ ℕ) (τ : T) :
    monoDeg e τ = ∑ k ∈ e.support.filter (fun k => k.1 = τ), e k := by
  unfold monoDeg
  congr

namespace ColIn

variable {B : Base} {X : PreX B.toPre} (I : ColIn B X)

def jetNum (a : I.ι) (u : B.Word) (i : ℕ) (N : Submodule (𝓞 B.fields.E) (Sp B.fields.E (B.R.N i)))
    (N' : Submodule (𝓞 B.fields.E) (Sp B.fields.E (B.R.N (i + 1)))) (c : ℕ) (x : HomE B.fields.E (B.R.N i) (B.R.N (i + 1)))
    (e : DVar B.fields.Tau (B.R.N i) (B.R.N (i + 1)) →₀ ℕ) : ℂ :=
  (I.A.chiF _ _ N N')⁻¹ * jetC I.A.cD (I.A.thInd (I.Sb a u) N N' c x) e

abbrev JetRange (a : I.ι) (u : B.Word) (i : ℕ) (N : Submodule (𝓞 B.fields.E) (Sp B.fields.E (B.R.N i)))
    (N' : Submodule (𝓞 B.fields.E) (Sp B.fields.E (B.R.N (i + 1)))) (c : ℕ) (x : HomE B.fields.E (B.R.N i) (B.R.N (i + 1))) : Prop :=
  letI := B.fields.starE
  InRange (I.Sb a u) (I.modulus a u) c N N' x

def JetsIn : Prop :=
  ∀ (a : I.ι) (u : B.Word) (i : ℕ), i < B.R.m →
    JetsRatDeg I.A (B.R.N i) (B.R.N (i + 1)) (Sall (Pr := B.primes X) I.sel (I.tup a) u)
      (cAof (Pr := B.primes X) I.sel (I.tup a) (I.cst a) * cBof (Pr := B.primes X) I.sel (I.tup a) (I.cst a) u)
      (fun τ => ∑ r, (B.wts.nuW u (i + 1) τ).w r)

theorem jetsIn_iff : I.JetsIn ↔ ∀ (a : I.ι) (u : B.Word) (i : ℕ), i < B.R.m → ∀ N N' c x,
    I.JetRange a u i N N' c x → ∀ e, (∀ τ, (monoDeg e τ : ℤ) = nuDeg B u i τ) →
      I.jetNum a u i N N' c x e ∈ B.embLL.fieldRange := by
  constructor
  · intro h a u i hi N N' c x hx e he
    obtain ⟨y, hy⟩ := h a u i hi N N' c x hx e (fun τ => by rw [← monoDeg_eq_sum_filter]; exact he τ)
    refine RingHom.mem_fieldRange.mpr ⟨y, ?_⟩
    rw [← I.A_σ₀]
    exact hy
  · intro h a u i hi N N' c x hx e he
    obtain ⟨y, hy⟩ := RingHom.mem_fieldRange.mp
      (h a u i hi N N' c x hx e (fun τ => by rw [monoDeg_eq_sum_filter]; exact he τ))
    refine ⟨y, ?_⟩
    rw [I.A_σ₀]
    exact hy

variable {I} {a : I.ι} {u : B.Word} {i : ℕ} {N : Submodule (𝓞 B.fields.E) (Sp B.fields.E (B.R.N i))}
  {N' : Submodule (𝓞 B.fields.E) (Sp B.fields.E (B.R.N (i + 1)))} {c : ℕ} {x : HomE B.fields.E (B.R.N i) (B.R.N (i + 1))}
  {e : DVar B.fields.Tau (B.R.N i) (B.R.N (i + 1)) →₀ ℕ}

theorem JetsIn.exists_eq (h : I.JetsIn) (hi : i < B.R.m) (hx : I.JetRange a u i N N' c x)
    (he : ∀ τ, (monoDeg e τ : ℤ) = nuDeg B u i τ) : ∃ y : B.LL, B.embLL y = I.jetNum a u i N N' c x e := by
  exact RingHom.mem_fieldRange.mp ((jetsIn_iff I).mp h a u i hi N N' c x hx e he)

end ColIn

end GlobalTheory.Mem.Col2

end
end

