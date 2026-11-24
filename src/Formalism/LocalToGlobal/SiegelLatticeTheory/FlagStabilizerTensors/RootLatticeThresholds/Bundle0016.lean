module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointQuot
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StepPtRepPfD
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TermTieOf
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle0006
public import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeGluingRadicals

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointQuotMeas
section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
attribute [-instance] PI.WSF.instMeasurableSpaceMat PI.WSF.instBorelSpaceMat
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal
open Matrix

set_option linter.dupNamespace false

namespace Formalism.L2.SG.Pf.Carrier.JointQuot

open Formalism.L2.SG.RealObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section PiProd


set_option backward.isDefEq.respectTransparency false in
theorem lintegral_fin_nat_prod {n : ℕ} {E : Fin n → Type*} {mE : ∀ i, MeasurableSpace (E i)}
    {μ : (i : Fin n) → Measure (E i)} [∀ i, SigmaFinite (μ i)] (f : (i : Fin n) → E i → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : Fin n) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc ∫⁻ x : (i : Fin (n + 1)) → E i, ∏ i, f i (x i) ∂(Measure.pi μ)
        = ∫⁻ x : E 0 × ((i : Fin n) → E (Fin.succ i)), f 0 x.1 * ∏ i : Fin n, f (Fin.succ i) (x.2 i)
            ∂((μ 0).prod (Measure.pi fun i => μ (Fin.succ i))) := by
          rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp_emb
            (MeasurableEquiv.measurableEmbedding _)]
          simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
            Fin.prod_univ_succ, Fin.insertNth_zero]
          simp
      _ = (∫⁻ x, f 0 x ∂(μ 0)) * ∏ i : Fin n, ∫⁻ x, f (Fin.succ i) x ∂(μ (Fin.succ i)) := by
          rw [← ih (fun i => f (Fin.succ i)) (fun i => hf _)]
          exact lintegral_prod_mul (hf 0).aemeasurable
            (Finset.measurable_prod _ fun i _ => (hf _).comp (measurable_pi_apply i)).aemeasurable
      _ = ∏ i, ∫⁻ x, f i x ∂(μ i) := by rw [Fin.prod_univ_succ]

theorem lintegral_fintype_prod {ι : Type*} [Fintype ι] {E : ι → Type*} {mE : ∀ i, MeasurableSpace (E i)}
    {μ : (i : ι) → Measure (E i)} [∀ i, SigmaFinite (μ i)] (f : (i : ι) → E i → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : ι) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  let e := (Fintype.equivFin ι).symm
  rw [← (measurePreserving_piCongrLeft μ e).lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  exact lintegral_fin_nat_prod (fun i => f (e i)) (fun i => hf _)

theorem pi_withDensity {ι : Type*} [Fintype ι] {E : ι → Type*} [∀ i, MeasurableSpace (E i)]
    (μ : (i : ι) → Measure (E i)) [∀ i, SigmaFinite (μ i)] (f : (i : ι) → E i → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) (hfin : ∀ i x, f i x ≠ ⊤) :
    Measure.pi (fun i => (μ i).withDensity (f i)) = (Measure.pi μ).withDensity (fun x => ∏ i, f i (x i)) := by
  haveI : ∀ i, SigmaFinite ((μ i).withDensity (f i)) := fun i =>
    SigmaFinite.withDensity_of_ne_top (Filter.Eventually.of_forall (hfin i))
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi,
    lintegral_fintype_prod _ hf]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [withDensity_apply _ (hs i)]

end PiProd

section WeilGen

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]

theorem weil_of_bruhat (μG μS : Measure G) [SigmaFinite μG] [SFinite μS] [μG.IsMulLeftInvariant]
    (B : G → ℝ≥0∞) (hBm : Measurable B) (hinv : μS.map (fun s => s⁻¹) = μS)
    (hb1 : ∀ x, ∫⁻ s, B (s * x) ∂μS = 1) (f : G → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ s, f (s * x) ∂μS) ∂(μG.withDensity B) := by
  have hF : Measurable fun p : G × G => f (p.1 * p.2) := hf.comp measurable_mul
  have hg : Measurable fun x => ∫⁻ s, f (s * x) ∂μS := hF.lintegral_prod_left'
  have hBinv : ∀ x, ∫⁻ s, B (s⁻¹ * x) ∂μS = 1 := by
    intro x
    have h1 : ∫⁻ s, B (s * x) ∂(μS.map fun s => s⁻¹) = ∫⁻ s, B (s⁻¹ * x) ∂μS :=
      lintegral_map (hBm.comp (measurable_mul_const x)) measurable_inv
    rw [← h1, hinv, hb1]
  rw [lintegral_withDensity_eq_lintegral_mul _ hBm hg]
  symm
  calc _ = ∫⁻ x, ∫⁻ s, B x * f (s * x) ∂μS ∂μG := by
        refine lintegral_congr fun x => ?_
        rw [Pi.mul_apply]
        exact (lintegral_const_mul _ (hf.comp (measurable_mul_const x))).symm
    _ = ∫⁻ s, ∫⁻ x, B x * f (s * x) ∂μG ∂μS :=
        lintegral_lintegral_swap
          ((hBm.comp measurable_fst).mul (hf.comp (measurable_snd.mul measurable_fst))).aemeasurable
    _ = ∫⁻ s, ∫⁻ x, B (s⁻¹ * x) * f x ∂μG ∂μS := by
        refine lintegral_congr fun s => ?_
        simpa only [inv_mul_cancel_left] using
          lintegral_mul_left_eq_self (μ := μG) (fun x => B (s⁻¹ * x) * f x) s
    _ = ∫⁻ x, ∫⁻ s, B (s⁻¹ * x) * f x ∂μS ∂μG :=
        lintegral_lintegral_swap
          ((hBm.comp (measurable_fst.inv.mul measurable_snd)).mul (hf.comp measurable_snd)).aemeasurable
    _ = ∫⁻ x, f x ∂μG := by
        refine lintegral_congr fun x => ?_
        rw [show ∫⁻ s, B (s⁻¹ * x) * f x ∂μS = (∫⁻ s, B (s⁻¹ * x) ∂μS) * f x from
          lintegral_mul_const _ (hBm.comp (measurable_inv.mul_const x)), hBinv, one_mul]

end WeilGen

variable {D : D7}

def NV (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) :
    Set (Formalism.REAL.UJ (X.B.I.ε v)) :=
  {g | Formalism.L2.SG.HidaSetting.InN (X.B.I.ε v) (fun a => Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR a))
    (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u)) (uMat g)}

def StV (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (γ : X.B.I.Ginf) (v : InfinitePlace X.B.I.F) :
    Set (Formalism.REAL.UJ (X.B.I.ε v)) :=
  StSet (NV X u v) (NV X u' v) (γ v)

def stCoordV (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (γ : X.B.I.Ginf)
    (v : InfinitePlace X.B.I.F) (y : Formalism.REAL.UJ (X.B.I.ε v)) : FreeE w → ℂ :=
  fun p => ((D.host.rdE : ℂ) ^ (D.R.rS - p.1.1.1)) *
    Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε v)
      (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.fR ⟨p.1.1.1, by have := p.2.1; omega⟩))
      (uMat ((γ v)⁻¹ * y * γ v) *ᵥ frm X u' D.host.rdE v p.1.2)

def muStabV (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (w : Point D.host.E (D.R.rS + 1)) : Measure (FreeE w → ℂ) :=
  Measure.pi fun _ => ENNReal.ofReal (D.host.ka / (X.B.g : ℝ) / Real.pi) • (volume : Measure ℂ)

def LocPinAt (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))
    (ν : ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v))) : Prop :=
  ∀ v, ∃ μRv : Measure (Formalism.REAL.UJ (X.B.I.ε v)), IsHaarLoc (StV X u u' (gamW X u u' w) v) μRv ∧
    IsQuotLoc μRv (ν v) ∧ μRv.map (stCoordV X u' w (gamW X u u' w) v) = muStabV X w

def LocPin (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))
    (νl : Point D.host.E (D.R.rS + 1) → ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v))) : Prop :=
  LocPinAt X u u' w (νl w)

def LocUni (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) : Prop :=
  ∀ w, OkPt X u u' w → ∀ μR : Measure X.B.I.Ginf,
    Formalism.L2.SG.HidaSetting.IsHaarOnSet X.B.I (StInf X u u' (gamW X u u' w)) μR →
    μR.map (stCoord X u' w (gamW X u u' w)) = muStab X w → ∀ v, ∃ μRv : Measure (Formalism.REAL.UJ (X.B.I.ε v)),
    IsHaarLoc (StV X u u' (gamW X u u' w) v) μRv ∧ μRv.map (fun s => s⁻¹) = μRv ∧
    μRv.map (stCoordV X u' w (gamW X u u' w) v) = muStabV X w ∧
    ∃ b : Formalism.REAL.UJ (X.B.I.ε v) → ℝ≥0∞, Measurable b ∧ (∀ x, b x ≠ ⊤) ∧ ∀ x, ∫⁻ s, b (s * x) ∂μRv = 1

def GlobProd (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) : Prop :=
  ∀ w, OkPt X u u' w → ∀ μR : Measure X.B.I.Ginf,
    Formalism.L2.SG.HidaSetting.IsHaarOnSet X.B.I (StInf X u u' (gamW X u u' w)) μR →
    μR.map (stCoord X u' w (gamW X u u' w)) = muStab X w →
    ∀ μRv : ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v)),
      (∀ v, IsHaarLoc (StV X u u' (gamW X u u' w) v) (μRv v) ∧
        (μRv v).map (stCoordV X u' w (gamW X u u' w) v) = muStabV X w) →
      μR = Measure.pi μRv

theorem ooQuot_pin (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word)
    (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (hN : NuQPin X u u' νq) (hR : StRel X u u')
    (hLU : LocUni X u u') (hGP : GlobProd X u u') :
    ∃ νl, (∀ w, OkPt X u u' w → LocPin X u u' w νl) ∧ Formalism.L2.SG.Pf.Carrier.JointPf.OOQuot X u u' νq νl := by
  have hI := stInv_of_rel X u u' hR
  have key : ∀ w : Point D.host.E (D.R.rS + 1),
      ∃ ν : ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v)), OkPt X u u' w →
        LocPinAt X u u' w ν ∧ ∀ y : ∀ v, X.Vloc u' v,
          (haveI := FiniteDimensional.complete ℂ (X.Vpi u);
            Formalism.L2.SG.TermOp.OO (νq (gamW X u u' w)) Set.univ (X.Wu u) (X.Wu u') (gamW X u u' w))
              (X.tensU u' y) =
          X.tensU u (fun v => (haveI := FiniteDimensional.complete ℂ (X.Vloc u v);
            Jv (ν v) (X.Wloc u v) (X.Wloc u' v) ((gamW X u u' w) v)) (y v)) := by
    intro w
    by_cases hw : OkPt X u u' w
    · obtain ⟨μR, hH, hQ, hM⟩ := hN.2 w hw.1
      haveI : SigmaFinite μR := hH.1
      choose μRv hHv hIv hMv b hbm hbt hb1 using hLU w hw μR hH hM
      have hprod : μR = Measure.pi μRv := hGP w hw μR hH hM μRv fun v => ⟨hHv v, hMv v⟩
      haveI : ∀ v, SigmaFinite (μRv v) := fun v => (hHv v).1
      have hσ : ∀ v, SigmaFinite ((Formalism.REAL.muG (X.B.I.ε v)).withDensity (b v)) :=
        fun v => SigmaFinite.withDensity_of_ne_top' (hbt v)
      have hBm : Measurable fun x : X.B.I.Ginf => ∏ v, b v (x v) :=
        Finset.measurable_prod _ fun v _ => (hbm v).comp (measurable_pi_apply v)
      have hb1G : ∀ x : X.B.I.Ginf, ∫⁻ s, (∏ v, b v ((s * x) v)) ∂μR = 1 := by
        intro x
        rw [hprod]
        have := lintegral_fintype_prod (μ := μRv) (fun v t => b v (t * x v))
          (fun v => (hbm v).comp (measurable_mul_const _))
        refine this.trans ?_
        exact Finset.prod_eq_one fun v _ => hb1 v (x v)
      have hinvG : μR.map (fun s => s⁻¹) = μR := by
        haveI : ∀ v, SigmaFinite ((μRv v).map (fun s => s⁻¹)) := fun v => by rw [hIv v]; infer_instance
        rw [hprod]
        have := Measure.pi_map_pi (μ := μRv) (f := fun _ s => s⁻¹) (fun v => measurable_inv.aemeasurable)
        refine this.trans ?_
        congr 1
        funext v
        exact hIv v
      have hp : Formalism.L2.SG.HidaSetting.IsQuotMeasS X.B.I μR
          (Measure.pi fun v => (Formalism.REAL.muG (X.B.I.ε v)).withDensity (b v)) := by
        intro f hf
        rw [pi_withDensity _ b hbm hbt]
        exact weil_of_bruhat (Formalism.L2.SG.ProjRows.muInf X.B.I) μR _ hBm hinvG hb1G f hf
      refine ⟨fun v => (Formalism.REAL.muG (X.B.I.ε v)).withDensity (b v), fun _ => ⟨fun v => ?_, fun y => ?_⟩⟩
      · refine ⟨μRv v, hHv v, fun f hf => ?_, hMv v⟩
        exact weil_of_bruhat (Formalism.REAL.muG (X.B.I.ε v)) (μRv v) (b v) (hbm v) (hIv v) (hb1 v) f hf
      · exact oo_eq_tens X u u' _ μR _ _ hH.2.2.1 _ hBm hb1G _ hσ hQ hp (hI w hw) y
    · exact ⟨fun v => Formalism.REAL.muG (X.B.I.ε v), fun h => absurd h hw⟩
  choose νl hνl using key
  exact ⟨νl, fun w hw => (hνl w hw).1, fun w hw hG y => (hνl w ⟨hw, hG⟩).2 y⟩

end Formalism.L2.SG.Pf.Carrier.JointQuot
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DFrameAtPfA
section
noncomputable section

open Matrix Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Carrier.DFrameAtPf

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut.PtRepPf

theorem exists_unitary_of_gram {k : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
    (α β : M →ₗ[ℂ] (Fin k → ℂ)) (h : ∀ p q, star (α p) ⬝ᵥ α q = star (β p) ⬝ᵥ β q) :
    ∃ ψ ∈ Matrix.unitaryGroup (Fin k) ℂ, ∀ p, ψ *ᵥ α p = β p := by
  let T : (Fin k → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin k) := (WithLp.linearEquiv 2 ℂ (Fin k → ℂ)).symm
  have hT : ∀ u v, inner ℂ (T u) (T v) = star u ⬝ᵥ v := by
    intro u v
    rw [dotProduct_comm]
    rfl
  let a : M →ₗ[ℂ] EuclideanSpace ℂ (Fin k) := T.toLinearMap ∘ₗ α
  let b : M →ₗ[ℂ] EuclideanSpace ℂ (Fin k) := T.toLinearMap ∘ₗ β
  have hab : ∀ p q, inner ℂ (a p) (a q) = inner ℂ (b p) (b q) := by
    intro p q
    simp only [a, b, LinearMap.comp_apply, LinearEquiv.coe_coe, hT, h]
  have hker : LinearMap.ker a ≤ LinearMap.ker b := by
    intro p hp
    rw [LinearMap.mem_ker] at hp ⊢
    have h2 := hab p p
    rw [hp, inner_zero_left, eq_comm, inner_self_eq_zero] at h2
    exact h2
  let g : LinearMap.range a →ₗ[ℂ] EuclideanSpace ℂ (Fin k) :=
    (LinearMap.ker a).liftQ b hker ∘ₗ (LinearMap.quotKerEquivRange a).symm.toLinearMap
  have hg : ∀ p, g ⟨a p, LinearMap.mem_range_self a p⟩ = b p := by
    intro p
    simp only [g, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply]
  have hgi : ∀ s t : LinearMap.range a, inner ℂ (g s) (g t) = inner ℂ s t := by
    rintro ⟨_, p, rfl⟩ ⟨_, q, rfl⟩
    rw [hg, hg, Submodule.coe_inner]
    exact (hab p q).symm
  let F := (g.isometryOfInner hgi).extend
  have hF : ∀ p, F (a p) = b p := by
    intro p
    have := LinearIsometry.extend_apply (g.isometryOfInner hgi) ⟨a p, LinearMap.mem_range_self a p⟩
    rw [LinearMap.coe_isometryOfInner, hg] at this
    exact this
  let ψ : Matrix (Fin k) (Fin k) ℂ :=
    LinearMap.toMatrix' (T.symm.toLinearMap ∘ₗ F.toLinearMap ∘ₗ T.toLinearMap)
  have hψ : ∀ u, ψ *ᵥ u = T.symm (F (T u)) := by
    intro u
    simp only [ψ, LinearMap.toMatrix'_mulVec, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearIsometry.coe_toLinearMap]
  have hiso : ∀ u v, star (ψ *ᵥ u) ⬝ᵥ (ψ *ᵥ v) = star u ⬝ᵥ v := by
    intro u v
    rw [← hT, ← hT, hψ, hψ, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
      LinearIsometry.inner_map_map]
  refine ⟨ψ, ?_, fun p => ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff']
    ext i j
    have := hiso (Pi.single i 1) (Pi.single j 1)
    simp [Matrix.mul_apply, dotProduct, Matrix.one_apply] at this ⊢
    rw [this]
    by_cases hij : i = j
    · subst hij
      simp [Pi.single_apply]
    · simp [Pi.single_apply, hij]
      exact Ne.symm hij
  · rw [hψ]
    have := hF p
    simp only [a, b, LinearMap.comp_apply, LinearEquiv.coe_coe] at this
    rw [this, LinearEquiv.symm_apply_apply]

section Lift

variable {n k : ℕ} (ε : Fin n → Bool)

def liftV (wb : Fin k → Fin n → ℂ) (U : Matrix (Fin k) (Fin k) ℂ) (y : Fin n → ℂ) : Fin n → ℂ :=
  y + ∑ a, ((U - 1) *ᵥ wCoord ε wb y) a • wb a

def liftL (wb : Fin k → Fin n → ℂ) (U : Matrix (Fin k) (Fin k) ℂ) : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) where
  toFun := liftV ε wb U
  map_add' x y := by
    have hw : wCoord ε wb (x + y) = wCoord ε wb x + wCoord ε wb y := by
      funext i; simp [wCoord, hJ_add_right]
    simp only [liftV, hw, mulVec_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
    abel
  map_smul' c x := by
    have hw : wCoord ε wb (c • x) = c • wCoord ε wb x := by
      funext i; simp [wCoord, hJ_smul_right]
    simp only [liftV, hw, mulVec_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, smul_add,
      Finset.smul_sum, smul_smul]

def liftM (wb : Fin k → Fin n → ℂ) (U : Matrix (Fin k) (Fin k) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toMatrix' (liftL ε wb U)

theorem liftM_mulVec (wb : Fin k → Fin n → ℂ) (U : Matrix (Fin k) (Fin k) ℂ) (y : Fin n → ℂ) :
    liftM ε wb U *ᵥ y = y + ∑ a, ((U - 1) *ᵥ wCoord ε wb y) a • wb a := by
  rw [liftM, LinearMap.toMatrix'_mulVec]; rfl

variable {ε}

theorem hJ_wb_sum {wb : Fin k → Fin n → ℂ} (hon : ∀ i j, hJ ε (wb i) (wb j) = if i = j then 1 else 0)
    (c : Fin k) (p : Fin k → ℂ) : hJ ε (wb c) (∑ a, p a • wb a) = p c := by
  rw [hJ_sum_right]
  simp only [hJ_smul_right, hon, mul_ite, mul_one, mul_zero]
  simp

theorem wCoord_liftM {wb : Fin k → Fin n → ℂ} (hon : ∀ i j, hJ ε (wb i) (wb j) = if i = j then 1 else 0)
    (U : Matrix (Fin k) (Fin k) ℂ) (y : Fin n → ℂ) :
    wCoord ε wb (liftM ε wb U *ᵥ y) = U *ᵥ wCoord ε wb y := by
  funext c
  show hJ ε (wb c) (liftM ε wb U *ᵥ y) = (U *ᵥ wCoord ε wb y) c
  rw [liftM_mulVec, hJ_add_right, hJ_wb_sum hon, sub_mulVec, one_mulVec, Pi.sub_apply]
  show wCoord ε wb y c + _ = _
  ring

theorem liftM_fix {wb : Fin k → Fin n → ℂ} (U : Matrix (Fin k) (Fin k) ℂ) (y : Fin n → ℂ)
    (hy : ∀ i, hJ ε (wb i) y = 0) : liftM ε wb U *ᵥ y = y := by
  have h0 : wCoord ε wb y = 0 := funext hy
  rw [liftM_mulVec, h0, mulVec_zero]
  simp

private theorem liftM_iso_lemma {wb : Fin k → Fin n → ℂ} (p : Fin k → ℂ) (y : Fin n → ℂ) :
    hJ ε (∑ a, p a • wb a) y = star p ⬝ᵥ wCoord ε wb y := by
  rw [hJ_sum_left]
  simp only [hJ_smul_left, dotProduct, wCoord, Pi.star_apply]

private theorem liftM_iso_lemma_2 {wb : Fin k → Fin n → ℂ} (p : Fin k → ℂ) (x : Fin n → ℂ) :
    hJ ε x (∑ a, p a • wb a) = star (wCoord ε wb x) ⬝ᵥ p := by
  rw [hJ_sum_right]
  simp only [hJ_smul_right, dotProduct, wCoord, Pi.star_apply, hJ_conj]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

private theorem liftM_iso_lemma_3 {wb : Fin k → Fin n → ℂ}
    (hon : ∀ i j, hJ ε (wb i) (wb j) = if i = j then 1 else 0) (q p : Fin k → ℂ) :
    hJ ε (∑ a, q a • wb a) (∑ a, p a • wb a) = star q ⬝ᵥ p := by
  rw [liftM_iso_lemma]
  congr 1
  funext c
  exact hJ_wb_sum hon c p

theorem liftM_iso {wb : Fin k → Fin n → ℂ} (hon : ∀ i j, hJ ε (wb i) (wb j) = if i = j then 1 else 0)
    (U : Matrix (Fin k) (Fin k) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin k) ℂ) (x y : Fin n → ℂ) :
    hJ ε (liftM ε wb U *ᵥ x) (liftM ε wb U *ᵥ y) = hJ ε x y := by
  have hu : Uᴴ * U = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.mp hU
    rwa [Matrix.star_eq_conjTranspose] at h
  have key : (U - 1) + (U - 1)ᴴ + (U - 1)ᴴ * (U - 1) = 0 := by
    simp only [conjTranspose_sub, conjTranspose_one, sub_mul, mul_sub, mul_one, one_mul, hu]
    abel
  rw [liftM_mulVec, liftM_mulVec, hJ_add_left, hJ_add_right, hJ_add_right, liftM_iso_lemma_3 hon,
    liftM_iso_lemma_2, liftM_iso_lemma]
  have e : ∀ a b : Fin k → ℂ, star a ⬝ᵥ ((U - 1) *ᵥ b) + (star ((U - 1) *ᵥ a) ⬝ᵥ b
      + star ((U - 1) *ᵥ a) ⬝ᵥ ((U - 1) *ᵥ b))
      = star a ⬝ᵥ (((U - 1) + (U - 1)ᴴ + (U - 1)ᴴ * (U - 1)) *ᵥ b) := by
    intro a b
    rw [star_mulVec, ← dotProduct_mulVec, ← dotProduct_mulVec, add_mulVec, add_mulVec,
      ← mulVec_mulVec, dotProduct_add, dotProduct_add]
    ring
  rw [add_assoc, e, key, zero_mulVec, dotProduct_zero, add_zero]

def liftU (wb : Fin k → Fin n → ℂ) (hon : ∀ i j, hJ ε (wb i) (wb j) = if i = j then 1 else 0)
    (U : Matrix (Fin k) (Fin k) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin k) ℂ) : Formalism.REAL.UJ ε :=
  ⟨(Matrix.isUnit_iff_isUnit_det _).2 (by
      have hA := inUJ_of_iso ε _ (liftM_iso hon U hU)
      unfold Formalism.REAL.inUJ at hA
      have h1 := congrArg Matrix.det hA
      rw [det_mul, det_mul] at h1
      have hJ0 : (Formalism.REAL.Jm ε).det ≠ 0 := by
        unfold Formalism.REAL.Jm
        rw [det_diagonal]
        exact Finset.prod_ne_zero_iff.2 fun a _ => by split_ifs <;> norm_num
      refine isUnit_iff_ne_zero.2 fun h0 => hJ0 ?_
      rw [← h1, show (liftM ε wb U).det = 0 from h0, mul_zero])|>.unit, inUJ_of_iso ε _ (liftM_iso hon U hU)⟩

theorem liftU_mulVec (wb : Fin k → Fin n → ℂ) (hon : ∀ i j, hJ ε (wb i) (wb j) = if i = j then 1 else 0)
    (U : Matrix (Fin k) (Fin k) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin k) ℂ) (y : Fin n → ℂ) :
    uMat (liftU wb hon U hU) *ᵥ y = liftM ε wb U *ᵥ y := rfl

end Lift

end Formalism.L2.SG.Pf.Carrier.DFrameAtPf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LeadingMinors
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.BridgeLemma Formalism.MainNotions.LatticeGluingRadicals

namespace Formalism.L2.SG.LeadingMinorsNonvanishing

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem leading_minor_ne_zero {D : D7} {T T' : ℕ} (hT : 0 < T) (F : LFlag (D.sp.Y 0) D.R.rS (T : D.host.E))
    (F' : LFlag (D.sp.Y 0) D.R.rS (T' : D.host.E)) (hz : F.zt = F.fl.z) (hz' : F'.zt = F'.fl.z) (hG : Gval F F' ≠ 0) :
    Dr1 F F' ≠ 0 := by
  intro h0
  obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
  have h1 := (b_G_pos (p_starConj D) hT F F' hz hz' hG (p_posX D T hT F) τ).1
  rw [b_tauG (p_starConj D) F F' τ, h0, map_zero, norm_zero, Complex.ofReal_re] at h1
  have h2 : (0:ℝ) ≤ (T:ℝ) * T' * ‖τ (Dr F F')‖ ^ 2 := by positivity
  nlinarith

theorem atSomeAll_holds : Formalism.L2.SG.TermTieOf.AtSomeAll := by
  intro D X Y u u' t hG hrel
  obtain ⟨F', ⟨hP, hmk⟩, hR⟩ := hrel
  have hf := Formalism.L2.SG.Closed.TermFun_holds D u u' (X.Fu u) _ ((Y.rowsOK u).1 t.lam t.mem)
  have hGv : Gval (lf D (X.Fu u)) F' ≠ 0 := by
    have e := Formalism.L2.SG.TermDef.Gt_mk hf.1 ⟨F', hP⟩
    rw [hmk] at e
    exact fun h0 => hG (e.trans h0)
  have hTu := tie_Tu_pos D u
  have hTu' := tie_Tu_pos D u'
  have hDr1 : Dl (lf D (X.Fu u)).fl F'.fl (D.R.rS + 1) ≠ 0 :=
    leading_minor_ne_zero hTu (lf D (X.Fu u)) F' rfl hP.1.2 hGv
  have geo := cell_geom D.host.F D.host.E (hS D) D.R.rS _ _ (lf D (X.Fu u)).fl F'.fl (tie_trace D.sp.cm)
    (tie_aniso D _ hTu (lf D (X.Fu u))) (tie_aniso D _ hTu' F') hR
  obtain ⟨p, hp⟩ := cell_of_matRel cell_inv cell_sign cell_bruhat cell_mono cell_point (le_refl (D.R.rS + 1))
    ((Zhat (lf D (X.Fu u)).fl F'.fl).submatrix (Fin.castLE (le_refl (D.R.rS + 1))) (Fin.castLE (le_refl (D.R.rS + 1))))
    (by rw [← tie_Dl_eq']; exact hDr1) (geo (D.R.rS + 1) le_rfl (Or.inr ⟨rfl, hGv⟩))
  refine ⟨p, F', ⟨hP, hmk⟩, hGv, ?_⟩
  obtain ⟨L, U, hL, hU, hZ⟩ := hp
  refine ⟨L, U, hL, hU, ?_⟩
  rw [← hZ]
  funext a b
  first
  | rfl
  | (simp [ZhatOM, ZhatL, Matrix.submatrix_apply]; rfl)

end Formalism.L2.SG.LeadingMinorsNonvanishing

end
end

