module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0031
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0350
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0444
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0351
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0301
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LvSameZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0273
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0263
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0418

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLineSimilitudeMapsSelfDualLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitLineSim

open GlobalTheory.FinPl

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_not_int : ∃ x : k, x ∉ 𝒪[k] := by
  obtain ⟨r, hr0, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  refine ⟨r⁻¹, fun h => ?_⟩
  have h1 : valuation k r⁻¹ ≤ 1 := h
  have hr : r ≠ 0 := hr0
  have : (1 : ValueGroupWithZero k) ≤ valuation k r := by
    calc (1 : ValueGroupWithZero k) = valuation k (r * r⁻¹) := by rw [mul_inv_cancel₀ hr, map_one]
      _ = valuation k r * valuation k r⁻¹ := map_mul _ _ _
      _ ≤ valuation k r * 1 := by gcongr
      _ = valuation k r := mul_one _
  exact absurd hr1 (not_lt.2 this)

theorem mul_sec' (q : SplitPt D k) (a : AE D) (b : k) : a * q.sec b = q.sec (q.pr a * b) := by
  rw [mul_comm, FrameLat.sec_mul_right, mul_comm]

theorem mul_csec (q : SplitPt D k) (a : AE D) (b : k) :
    a * cA D (q.sec b) = cA D (q.sec (q.pr (cA D a) * b)) := by
  rw [← mul_sec', map_mul, Formalism.L2.Theta.cA_cA]

theorem mulVec_sec' (q : SplitPt D k) {m n : ℕ} (M : Matrix (Fin m) (Fin n) (AE D)) (A : Fin n → k) :
    (M *ᵥ fun i => q.sec (A i)) = fun j => q.sec ((M.map q.pr *ᵥ A) j) := by
  funext j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, mul_sec', map_sum]

theorem mulVec_csec (q : SplitPt D k) {m n : ℕ} (M : Matrix (Fin m) (Fin n) (AE D)) (B : Fin n → k) :
    (M *ᵥ fun i => cA D (q.sec (B i))) = fun j => cA D (q.sec ((M.map (fun a => q.pr (cA D a)) *ᵥ B) j)) := by
  funext j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, mul_csec, map_sum]

theorem pr_cA_sec (q : SplitPt D k) (c : k) : q.pr (cA D (q.sec c)) = 0 := by
  have he : q.pr (cA D q.e) = 0 := by
    have h1 : q.pr (cA D q.e * q.e) = 0 := by rw [FrameLat.cAe_mul_e, map_zero]
    have pe : q.pr q.e = 1 := by rw [← FrameLat.sec_one, q.pr_sec]
    rwa [map_mul, pe, mul_one] at h1
  rw [← FrameLat.e_mul_sec q c, map_mul, map_mul, he, zero_mul]

theorem pr_cA_xi_int (q : SplitPt D k) (h : q.UnitAA) : q.pr (cA D (incA D D.host.xi0)) ∈ 𝒪[k] := by
  have hid : cA D (q.sec 1) ∈ idAt D (· = q.v) := FrameLat.csec_mem_idAt (p := q) 1
  have hc : cA D (q.sec 1) ∈ intAt D (· = q.v) := by
    refine (GlobalTheory.SplitIntComp.mem_intAt_iff q hid).2 ⟨?_, ?_⟩
    · rw [pr_cA_sec]; exact zero_mem _
    · rw [Formalism.L2.Theta.cA_cA, q.pr_sec]; exact one_mem _
  have h2 := (h.1 _ hc).1
  have h3 := ((GlobalTheory.SplitIntComp.mem_intAt_iff q h2.1).1 h2).2
  rwa [map_mul, Formalism.L2.Theta.cA_cA, map_mul, q.pr_sec, mul_one] at h3

theorem pr_xi_int (q : SplitPt D k) (h : q.UnitAA) : q.pr (incA D D.host.xi0) ∈ 𝒪[k] :=
  (GlobalTheory.SplitIntComp.val_xi q h).le

end GlobalTheory.SplitLineSim

namespace GlobalTheory.SplitLineSim
open GlobalTheory.FinPl

theorem line_sim_maps : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (L L'' : HSp D) (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (LL : GlobalTheory.FinPl.Lat L) (LZ : GlobalTheory.FinPl.Lat L'') (zL : Fin L.rank → k) (z₀ : Fin L''.rank → k) (u : k), q.UnitAA → IsSelfDualC L LL → IsSelfDualC L'' LZ → L.rank = 1 → L''.rank = 1 → (∀ y : k, y ∈ 𝒪[k] ↔ (fun i => q.sec (zL i * y)) ∈ GlobalTheory.FinPl.latV L LL (· = q.v)) → (∀ y : k, y ∈ 𝒪[k] ↔ (fun i => q.sec (z₀ i * y)) ∈ GlobalTheory.FinPl.latV L'' LZ (· = q.v)) → valuation k u = 1 → τ.map (ofSplit q).pr *ᵥ z₀ = u • zL → τᴴ * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram → ∀ y ∈ GlobalTheory.FinPl.latV L'' LZ (· = q.v), (rat τ : Mx D L.rank L''.rank) *ᵥ y ∈ GlobalTheory.FinPl.latV L LL (· = q.v) := by
  intro D k _ _ _ _ q L L'' τ LL LZ zL z₀ u hU hLL hLZ hr hr'' hcL hcZ hu hτz hτ y hy
  haveI : Unique (Fin L.rank) := ⟨⟨⟨0, by omega⟩⟩, fun j => Fin.ext (by have := j.2; omega)⟩
  haveI : Unique (Fin L''.rank) := ⟨⟨⟨0, by omega⟩⟩, fun j => Fin.ext (by have := j.2; omega)⟩
  set j0 : Fin L.rank := default with hj0
  set i0 : Fin L''.rank := default with hi0
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, map_zero] at hu
    exact zero_ne_one hu
  have hu_int : u ∈ 𝒪[k] := hu.le
  have hui_int : u⁻¹ ∈ 𝒪[k] := by
    show valuation k u⁻¹ ≤ 1
    rw [map_inv₀, hu, inv_one]

  have h1 : q.pr (incA D (τ j0 i0)) * z₀ i0 = u * zL j0 := by
    have := congrFun hτz j0
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Fintype.sum_unique, Pi.smul_apply, smul_eq_mul] at this
    exact this
  have hzL : zL j0 ≠ 0 := by
    intro h0
    obtain ⟨x, hx⟩ := exists_not_int (k := k)
    apply hx
    rw [hcL]
    have : (fun i => q.sec (zL i * x)) = 0 := by
      funext i
      rw [Subsingleton.elim i j0, h0, zero_mul, map_zero]
      rfl
    rw [this]
    exact zero_mem _
  have hz0 : z₀ i0 ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h1
    exact hzL ((mul_eq_zero.1 h1.symm).resolve_left hu0)

  have hyS : ∀ i, y i ∈ idAt D (· = q.v) := FrameLat.latV_supp hy
  set A : Fin L''.rank → k := fun i => q.pr (y i) with hA
  set B : Fin L''.rank → k := fun i => q.pr (cA D (y i)) with hB
  have hyAB : y = (fun i => q.sec (A i)) + fun i => cA D (q.sec (B i)) := by
    funext i
    exact GlobalTheory.SplitIntComp.eq_sec_add_csec q (hyS i)
  rw [hyAB] at hy
  obtain ⟨hyA, hyB⟩ := (FrameLat.decomp hLZ A B).1 hy
  rw [hyAB, Matrix.mulVec_add, mulVec_sec', mulVec_csec]
  refine (FrameLat.decomp hLL _ _).2 ⟨?_, ?_⟩
  ·
    set c : k := A i0 / z₀ i0 with hc
    have hcA : ∀ i, z₀ i * c = A i := fun i => by
      rw [Subsingleton.elim i i0, hc, mul_div_cancel₀ _ hz0]
    have hcint : c ∈ 𝒪[k] := (hcZ c).2 (by simpa only [hcA] using hyA)
    have : (fun j => q.sec ((((rat τ : Mx D L.rank L''.rank)).map q.pr *ᵥ A) j)) =
        fun j => q.sec (zL j * (u * c)) := by
      funext j
      rw [Subsingleton.elim j j0]
      congr 1
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Fintype.sum_unique]
      rw [← hcA i0]
      change q.pr (incA D (τ j0 i0)) * (z₀ i0 * c) = _
      rw [← mul_assoc, h1]
      ring
    rw [this]
    exact (hcL _).1 (mul_mem hu_int hcint)
  ·
    rw [FrameLat.csec_mem_iff hLL]
    intro x hx
    have h00 : star (τ j0 i0) * (L.gram j0 j0 * τ j0 i0) = -(D.host.xi0 * star D.host.xi0) * L''.gram i0 i0 := by
      have := congrFun (congrFun hτ i0) i0
      rw [Matrix.mul_apply, Fintype.sum_unique, Matrix.mul_apply, Fintype.sum_unique,
        Matrix.conjTranspose_apply, Matrix.smul_apply, smul_eq_mul] at this
      exact this
    let φ : D.host.E →+* k := (q.pr.comp (cA D)).comp (incA D)
    have hφs : ∀ t : D.host.E, φ (star t) = q.pr (incA D t) := fun t => by
      show q.pr (cA D (incA D (star t))) = _
      rw [FrameLat.cA_incA, star_star]

    have e3 : q.pr (incA D (τ j0 i0)) * (q.pr (cA D (incA D (L.gram j0 j0))) * q.pr (cA D (incA D (τ j0 i0)))) =
        -(q.pr (cA D (incA D D.host.xi0)) * q.pr (incA D D.host.xi0)) * q.pr (cA D (incA D (L''.gram i0 i0))) := by
      have h2 := congrArg φ h00
      rw [map_mul, map_mul, map_mul, map_neg, map_mul, hφs (τ j0 i0), hφs D.host.xi0] at h2
      exact h2
    have hcw_int : -(q.pr (cA D (incA D D.host.xi0)) * q.pr (incA D D.host.xi0)) ∈ 𝒪[k] :=
      neg_mem (mul_mem (pr_cA_xi_int q hU) (pr_xi_int q hU))
    obtain ⟨c', hc'⟩ : ∃ c' : k, c' = x j0 / zL j0 := ⟨_, rfl⟩
    have hxc : ∀ j, zL j * c' = x j := fun j => by
      rw [Subsingleton.elim j j0, hc', mul_div_cancel₀ _ hzL]
    have hc'int : c' ∈ 𝒪[k] := (hcL c').2 (by simpa only [hxc] using hx)

    have hz1 : (fun i => q.sec (z₀ i)) ∈ latV L'' LZ (· = q.v) := by
      simpa only [mul_one] using (hcZ 1).1 (one_mem _)
    have hZB := (FrameLat.csec_mem_iff hLZ B).1 hyB z₀ hz1
    simp only [Fintype.sum_unique] at hZB
    have hinv : u * u⁻¹ = 1 := mul_inv_cancel₀ hu0
    have e0 : ((((rat τ : Mx D L.rank L''.rank)).map (fun a => q.pr (cA D a)) *ᵥ B) j0) =
        q.pr (cA D (incA D (τ j0 i0))) * B i0 := by
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Fintype.sum_unique]
      rfl
    simp only [Fintype.sum_unique]
    rw [e0, ← hxc j0]
    have key : zL j0 * c' * q.pr (cA D (incA D (L.gram j0 j0))) * (q.pr (cA D (incA D (τ j0 i0))) * B i0) =
        c' * u⁻¹ * (-(q.pr (cA D (incA D D.host.xi0)) * q.pr (incA D D.host.xi0))) *
          (z₀ i0 * q.pr (cA D (incA D (L''.gram i0 i0))) * B i0) := by
      linear_combination (c' * u⁻¹ * z₀ i0 * B i0) * e3 -
        (c' * u⁻¹ * q.pr (cA D (incA D (L.gram j0 j0))) * q.pr (cA D (incA D (τ j0 i0))) * B i0) * h1 -
        (c' * q.pr (cA D (incA D (L.gram j0 j0))) * q.pr (cA D (incA D (τ j0 i0))) * B i0 * zL j0) * hinv
    rw [key]
    exact mul_mem (mul_mem (mul_mem hc'int hui_int) hcw_int) hZB

end GlobalTheory.SplitLineSim
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepBeforeLastEqSSucc
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel

noncomputable section
namespace GlobalTheory.PenBridge

section Local
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type} [Fintype n] [DecidableEq n]

def toSum0 (k : Type) [Field k] (n : Type) [Fintype n] [DecidableEq n] : GL n k ≃* GL (n ⊕ Fin 0) k :=
  Units.mapEquiv (Matrix.reindexAlgEquiv k k (Equiv.sumEmpty n (Fin 0)).symm).toMulEquiv

theorem toSum0_val (g : GL n k) :
    ((toSum0 k n g : GL (n ⊕ Fin 0) k) : Matrix (n ⊕ Fin 0) (n ⊕ Fin 0) k) =
      (g : Matrix n n k).reindex (Equiv.sumEmpty n (Fin 0)).symm (Equiv.sumEmpty n (Fin 0)).symm := rfl

end Local

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)}
  {hT : GatTies (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {Gi : Formalism.MainNotions.G.Inst (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) L} {Gl : Formalism.MainNotions.G.LatInst (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {cX : ExtraC} {ex : Extra (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : B.Word}
  {a : GeoAll W u} {t : W.P.T}

theorem step_before_last_eq_s_succ (J : QJ a t) {j : ℕ} (hj : j + 1 = B.R.m) (i : Fin J.r) : j = (J.G i).s + 1 := by
  have h1 := (J.G i).hs
  have h2 : (I.rec7 l Z).R.m = B.R.m := rfl
  have h3 : (GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).R.m = B.R.m := rfl
  omega

def frJ (J : QJ a t) (j : ℕ) (i : Fin J.r) (e : j = (J.G i).s + 1) :
    Frame (J.G i).k ((I.rec7 l Z).sp.X j).rank (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) ((J.G i).s + 1)) := by
  subst e
  exact (J.G i).FX _ le_rfl

def rdAt (J : QJ a t) (j : ℕ) (i : Fin J.r) (e : j = (J.G i).s + 1) :
    GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) →*
      GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) ((J.G i).s + 1) ⊕ Fin 0) (J.G i).k :=
  (toSum0 (J.G i).k _).toMonoidHom.comp (GlobalTheory.LevIdx.locHom (J.G i).q _ (frJ J j i e))

def rd (J : QJ a t) (j : ℕ) (hj : j + 1 = B.R.m) :
    GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) →*
      ((i : Fin J.r) → GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) ((J.G i).s + 1) ⊕ Fin 0) (J.G i).k) :=
  MonoidHom.pi fun i => rdAt J j i (step_before_last_eq_s_succ J hj i)

def plF (J : QJ a t) (p : GlobalTheory.FinPl.Pl (I.rec7 l Z)) : Prop := ∃ i, (J.G i).q.v = p

end GlobalTheory.PenBridge
end

namespace GlobalTheory.PenBridge

section Local
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type} [Fintype n] [DecidableEq n]

theorem toSum0_mem_KO_iff (x : GL n k) : toSum0 k n x ∈ KO k (n ⊕ Fin 0) ↔ x ∈ KO k n := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨Units.mapEquiv (Matrix.reindexAlgEquiv 𝒪[k] 𝒪[k] (Equiv.sumEmpty n (Fin 0))).toMulEquiv y, ?_⟩
    ext a b
    have := congrArg (fun g : GL (n ⊕ Fin 0) k => (g : Matrix (n ⊕ Fin 0) (n ⊕ Fin 0) k) (Sum.inl a) (Sum.inl b)) hy
    simpa [toSum0_val, Matrix.reindex_apply] using this
  · rintro ⟨y, rfl⟩
    refine ⟨Units.mapEquiv (Matrix.reindexAlgEquiv 𝒪[k] 𝒪[k] (Equiv.sumEmpty n (Fin 0)).symm).toMulEquiv y, ?_⟩
    ext a b
    simp [toSum0_val, Matrix.reindex_apply]

end Local

theorem relIndex_comap_conj {G : Type} [Group G] (H K : Subgroup G) {c : G} (hc : c ∈ K) :
    (H.comap (MulAut.conj c).toMonoidHom).relIndex K = H.relIndex K := by
  rw [Subgroup.relIndex_comap]
  congr 1
  ext x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact K.mul_mem (K.mul_mem hc hy) (K.inv_mem hc)
  · intro hx
    exact ⟨c⁻¹ * x * c, K.mul_mem (K.mul_mem (K.inv_mem hc) hx) hc, by group⟩

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)}
  {hT : GatTies (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {Gi : Formalism.MainNotions.G.Inst (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) L} {Gl : Formalism.MainNotions.G.LatInst (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {cX : ExtraC} {ex : Extra (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : B.Word}
  {a : GeoAll W u} {t : W.P.T}

end GlobalTheory.PenBridge
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepZeroRamifiedFormsTransportIff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RamZero

open GlobalTheory.Mem.Col2.TwAtStd

theorem levelZero_classTransport_values {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (u : B.Word) (a : I.ι) (ψ₀ : ((I.rec7 l Z).mem u).C.cls 0 → ((I.rec7 l Z).mem u).C.Y 0 → ℂ)
    (c : (I.stp u I.mu0 0).Cl) :
    (I.rec7 l Z).e0Tw u a ψ₀ (I.eCls0 l u a c) = ψ₀ c := by
  show ψ₀ ((I.eCls0 l u a).symm (I.eCls0 l u a c)) = ψ₀ c
  rw [Equiv.symm_apply_apply]

theorem mram_iff_ramT : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), I.Law0 l → ∀ (u : B.Word) (a : I.ι) (ψ₀ : ((I.rec7 l Z).mem u).C.cls 0 → ((I.rec7 l Z).mem u).C.Y 0 → ℂ), ψ₀ ∈ ((I.rec7 l Z).mem u).A.Mram ↔ GlobalTheory.AdForm.RamT (I := I) (l := l) (u := u) (a := a) 0 ((I.rec7 l Z).e0Tw u a ψ₀) := by
  intro B X I hI l Z _ u a ψ₀
  have hval := levelZero_classTransport_values I l Z u a ψ₀
  have e1 := mem_Fi_of_free (I.stp u I.mu0 0) B.fields.emb B.embLL (lamT (B.hcW u) 0) (l.lev u I.mu0).free0 ψ₀
  have e2 := mem_Fi_of_free (I.stp u a 0) B.fields.emb B.embLL (lamT (B.hcW u) 0) (l.lev u a).free0
    ((I.rec7 l Z).e0Tw u a ψ₀)
  have hFi : ψ₀ ∈ ((I.rec7 l Z).mem u).A.Mu0 ↔ (I.rec7 l Z).e0Tw u a ψ₀ ∈ (I.fm l u a).Fi 0 := by
    refine e1.trans (Iff.trans ⟨fun h c' => ?_, fun h c => ?_⟩ e2.symm)
    · obtain ⟨c, rfl⟩ := (I.eCls0 l u a).surjective c'
      have := h c
      rw [← hval c] at this
      exact this
    · have := h (I.eCls0 l u a c)
      rw [hval c] at this
      exact this
  have hN : ∀ (v : ((I.rec7 l Z).mem u).A.vT) (c : (I.stp u I.mu0 0).Cl),
      ∑ᶠ s : ((I.atT l u a).Fv v)ˣ, (I.fm l u a).dilT 0 v s (I.eCls0 l u a c)
        ((I.rec7 l Z).e0Tw u a ψ₀ ((I.fm l u a).dil 0 v s (I.eCls0 l u a c))) = ((I.rec7 l Z).mem u).A.Nm v ψ₀ c := by
    intro v c
    have eR : ∀ c' : ((I.rec7 l Z).mem u).C.cls 0, ((I.rec7 l Z).mem u).A.Nm v ψ₀ c' =
        ∑ s, (((I.rec7 l Z).fm u).dilT 0 v s c') (ψ₀ (((I.rec7 l Z).fm u).dil 0 v s c')) := fun c' => by
      unfold ColumnsAtT.Nm
      rw [LinearMap.sum_apply, Finset.sum_apply]
      exact Finset.sum_congr rfl fun x _ => ((I.rec7 l Z).fm u).rhoT_dil v x ψ₀ c'
    rw [eR c]
    letI := (I.atT l u a).FvFin v
    letI := (I.atT l u a).FvDec v
    rw [finsum_eq_sum_of_fintype]
    refine Fintype.sum_equiv (Equiv.refl _) _ _ fun s => ?_
    show (I.atIn u a).dilT B.fields.emb B.embLL 0 v s (I.eCls0 l u a c)
        ((I.rec7 l Z).e0Tw u a ψ₀ ((I.atIn u a).dil 0 v s (I.eCls0 l u a c))) =
      (I.atIn u I.mu0).dilT B.fields.emb B.embLL 0 v s c (ψ₀ ((I.atIn u I.mu0).dil 0 v s c))
    rw [dil_eCls0 B X I hI l u a v s c, dilT_eCls0 B X I hI l u a v s c, hval]
  unfold ColumnsAtT.Mram GlobalTheory.AdForm.RamT
  rw [Submodule.mem_inf, Submodule.mem_iInf]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨hFi.1 h1, fun v c' => ?_⟩
    obtain ⟨c, rfl⟩ := (I.eCls0 l u a).surjective c'
    refine (hN v c).trans ?_
    exact congrFun (LinearMap.mem_ker.1 (h2 v)) c
  · rintro ⟨h1, h2⟩
    exact ⟨hFi.2 h1, fun v => LinearMap.mem_ker.2 (funext fun c => (hN v c).symm.trans (h2 v (I.eCls0 l u a c)))⟩

end GlobalTheory.RamZero

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepZeroRepresentativeDiffersByLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.RepZero

open _root_.Formalism.L2.Col GlobalTheory.Mem.Col2.StepZero

theorem chr_of_down_eq_one {X : Fields} {n : ℕ} {ST SG Q : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers X.E))}
    {y : Ys X n} {β : Type} [Fintype β] [DecidableEq β] {Λ : β → LevFam X.E X.K n SG} {Θ : β → LevQFam X.E X.K n Q}
    (pref : DecoF X.E n ST SG Q → Prop) {Λ₀ : LevFam X.E X.K n SG} (hΛ : ∀ b, Λ b = Λ₀) (hΘ : ∀ b, Θ b = LevQFam.top X.E X.K n Q)
    (b : β) (g : (stepY ST y β Λ Θ pref).G b) (h : down pref hΛ b g = 1) : (stepY ST y β Λ Θ pref).chr b g = 1 := by
  show (Λ b).chr g.2.1 * (Θ b).chr g.2.2 = 1
  rw [chr_eq_one (hΘ b), mul_one, chr_congr (hΛ b)]
  have e : (⟨g.2.1.1, hΛ b ▸ g.2.1.2⟩ : Λ₀.grp) = (down pref hΛ b g).2 := rfl
  rw [e, h]
  exact map_one _

theorem exists_lift_one {X : Fields} {n : ℕ} {ST SG Q : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers X.E))}
    {y : Ys X n} {β : Type} [Fintype β] [DecidableEq β] {Λ : β → LevFam X.E X.K n SG} {Θ : β → LevQFam X.E X.K n Q}
    (pref : DecoF X.E n ST SG Q → Prop) {Λ₀ : LevFam X.E X.K n SG} (hy : ∀ N, y.ys N = {∅}) (hΛ : ∀ b, Λ b = Λ₀)
    (hΘ : ∀ b, Θ b = LevQFam.top X.E X.K n Q) (b : β) (p q : (stepY ST y β Λ Θ pref).D b) (h : p.1.1.deco = q.1.1.deco) :
    ∃ g : (stepY ST y β Λ Θ pref).G b, (stepY ST y β Λ Θ pref).gam b g = 1 ∧ g • p = q ∧ (stepY ST y β Λ Θ pref).chr b g = 1 := by
  obtain ⟨g, h2, h3⟩ := exists_lift pref hy hΛ hΘ b p q 1 (by rw [one_smul]; exact h)
  exact ⟨g, (congrArg (fun g => ufGL X.E n g.1) h2).trans (map_one _), h3, chr_of_down_eq_one pref hΛ hΘ b g h2⟩

end GlobalTheory.Fam.RepZero


set_option maxHeartbeats 4000000 in
theorem GlobalTheory.Fam.rep_zero_std : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (C : Formalism.L2.Forms.ColsTiedSym (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)), I.StdC l Z C → ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ (β : Ch 0), A.kb 0 β = TC.kStd X u (B.R.N 0) → ∀ c : {c // A.chOf 0 c = β}, ∃ κ : (A.K 0 (Nat.zero_le _) β).lev.U, ((C.forms u).to0.cls0.y ((I.eCls0 l u a).symm c.1)).1 = ((A.K 0 (Nat.zero_le _) β).y c).1 * κ.1 ∧ (A.K 0 (Nat.zero_le _) β).lev.chi κ = 1 := by
  set_option maxHeartbeats 4000000 in
    intro B X I hI _ l Z C hC u a Ch A hA β hk c
    obtain ⟨c, rfl⟩ := c
    set c' := (I.eCls0 l u a).symm c with hc'
    have hR := hA.reads 0 (Nat.zero_le _)
    have hyS : ((C.forms u).to0.cls0.y c').1 = I.yStd u 0 c' := (hC u).yE 0 (Nat.zero_le _) (Or.inl rfl) c'
    have hS := MemChart.yStd_spec I hI u 0 c'
    set yc : TC.GA B (B.R.N 0) := ((A.K 0 (Nat.zero_le _) (A.chOf 0 c)).y ⟨c, rfl⟩).1 with hyc
    have hd : Disjoint (B.primes X).vGs (I.Q a) := (LevTwist.levOk_twists B X I hI).2.1.mono_right (I.Q_subset_SQ a)
    let q : Formalism.L2.Col.ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u 0 := extTo (I.Q a) (extTo I.SQ ((I.stp u I.mu0 0).rep c').1.1)
    have hq : TC.PtOf (yc * (yc⁻¹ * I.yStd u 0 c') * A.kb 0 (A.chOf 0 c)) q := by
      rw [mul_inv_cancel_left, hk]
      exact IsPtOf.extTo (I.Q_subset_SQ a) hd hS
    have hL := hI.idx_ok a
    have hy := StepZero.ysAt_zero I.sel (I.tup a) (I.cst a) (R := B.R)
    have hΛ := StepZero.levGAt_zero (I.Tp a) hL
    have hΘ := StepZero.levQAt_zero (I.Tp a) hL
    have e : ((I.stp u a 0).rep c).1.1.deco = ((I.stp u I.mu0 0).rep c').1.1.deco := by
      have := TC.StepZero.rep_eCls0 I hI l u a c'
      rwa [hc', Equiv.apply_symm_apply] at this
    obtain ⟨p, hp⟩ := exists_ptAt (R := B.R) I.sel (I.tup a) (I.cst a) q
    obtain ⟨g, hgam, h3, hchr⟩ := RepZero.exists_lift_one ((I.Tp a).pref u 0) hy hΛ hΘ c.1 ((I.stp u a 0).rep c) p
      (by rw [hp]; exact e)
    have hact : ((I.stp u a 0).act c.1 g ((I.stp u a 0).rep c)).1.1 = q :=
      (congrArg (fun p : PtAt B.R I.sel (I.tup a) (I.cst a) u 0 => p.1.1) h3).trans hp
    have hmem : yc⁻¹ * I.yStd u 0 c' ∈ (A.K 0 (Nat.zero_le _) (A.chOf 0 c)).lev.U :=
      (hR.lev c _ q hq).2 ⟨g, hgam, hact, TC.Chart0.cos0 I _ _⟩
    refine ⟨⟨yc⁻¹ * I.yStd u 0 c', hmem⟩, ?_, ?_⟩
    · show _ = yc * (yc⁻¹ * I.yStd u 0 c')
      rw [hyS, mul_inv_cancel_left]
    · have hpt2 : TC.PtOf (yc * (yc⁻¹ * I.yStd u 0 c') * A.kb 0 (A.chOf 0 c))
          ((I.stp u a 0).act c.1 g ((I.stp u a 0).rep c)).1.1 := by
        rw [hact]
        exact hq
      have hc := hR.chr c ⟨yc⁻¹ * I.yStd u 0 c', hmem⟩ g hgam hpt2
      apply Units.ext
      refine hc.trans ?_
      rw [hchr]
      simp
end

