module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0022
public import Formalism.LocalToGlobal.IndefiniteReal.SquareIntegrableTransfer
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHLeaf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0020
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ActMass
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RightActionThreeFamilies
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowFrameCoherence.Bundle0002
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0017
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0010
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.SubMemOfIndQ
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0033

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTReg
section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
attribute [-instance] PI.WSF.instMeasurableSpaceMat PI.WSF.instBorelSpaceMat
noncomputable section

open MeasureTheory
open scoped InnerProductSpace ComplexConjugate

namespace Formalism.L2.SG.EvalTReg

section Abs

open Formalism.MainNotions.LeviCoordinates

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
  {μ : Measure G} [SigmaFinite μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
  {Γ : Subgroup G} [Countable Γ] {D : Set G}

theorem reg_toLp (h : rr_FD μ Γ D) {R : G → (Lp ℂ 2 (μ.restrict D) →L[ℂ] Lp ℂ 2 (μ.restrict D))}
    (hR : rr_IsReg μ Γ D R) (f0 : G → ℂ) (hinv : ∀ γ ∈ Γ, ∀ y, f0 (γ * y) = f0 y)
    (hm : MemLp f0 2 (μ.restrict D)) (g : G) :
    ((R g (hm.toLp f0) : Lp ℂ 2 (μ.restrict D)) : G → ℂ) =ᵐ[μ.restrict D] fun x => f0 (x * g) := by
  have hmap := rr_map h g
  have h3 : ∀ᵐ x ∂(μ.restrict D), (hm.toLp f0 : G → ℂ) (rr_rep (Γ : Set G) D (x * g)) =
      f0 (rr_rep (Γ : Set G) D (x * g)) := by
    refine ae_of_ae_map (p := fun y => (hm.toLp f0 : G → ℂ) y = f0 y) hmap.1 ?_
    rw [hmap.2]
    exact hm.coeFn_toLp
  filter_upwards [hR g (hm.toLp f0), h3] with x a1 a2
  rw [a1, a2]
  obtain ⟨γ, hγ, e1, -⟩ := rr_rep_spec h (x * g)
  rw [e1, hinv γ hγ]

end Abs

section X

open Formalism.BasicNotions Formalism.MainNotions.LeviCoordinates Formalism.L2.SG.RowDict Formalism.L2.SG.Pf

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem reg_toLp_X (f0 : X.B.I.GA → ℂ) (hinv : ∀ γ ∈ X.B.I.GFset, ∀ y, f0 (γ * y) = f0 y)
    (hm : MemLp f0 2 (muX X)) (y : X.B.I.GA) :
    ((X.B.R y (hm.toLp f0) : L2X X) : X.B.I.GA → ℂ) =ᵐ[muX X] fun x => f0 (x * y) := by
  have := X.B.sf
  have := X.B.haar
  have := gf_secondCountable X.B.I
  have := muf_right X
  have := rr_muA_sigmaFinite X.B.I X.B.μf
  have := rr_muA_left X.B.I X.B.μf
  have := rr_muA_right X.B.I X.B.μf
  exact reg_toLp (rr_FD_of X.B.I X.B.μf X.B.fund X.B.fund_spec)
    (rr_IsReg_of X.B.I X.B.μf X.B.fund X.B.R X.B.R_spec) f0 hinv hm y

end X

section Polar

variable {α : Type*} [MeasurableSpace α] {ν : Measure α}

end Polar

section Transfer

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {μ : Measure (GA D (D.sp.Y 0))} {𝓕 : Set (GA D (D.sp.Y 0))} {X : Formalism.L2.SG.HidaSetting.HidaSetting D}
  {ι : GA D (D.sp.Y 0) ≃* X.B.I.GA} {t : GA D (D.sp.Y 0)} {c : ℝ}

end Transfer

end Formalism.L2.SG.EvalTReg

end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LiftMassCOf
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.Full

namespace Formalism.L2.SG.Pf.FibreCounting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Count

variable {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word}

theorem autLz_finite (hN : Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u' Y.hK) {Λ' : Submodule (𝓞 D.host.E) (VS D).V}
    (hΛ' : Λ' ∈ Y.what₂ u') : Finite (autLz D (X.Fu u') Λ') := by
  let q : {Λ // Λ ∈ Y.what₂ u'} := ⟨Λ', hΛ'⟩
  have e1 := Equiv.ofBijective _ (Formalism.L2.SG.Pf.Act.gamL_autLz_bij (Y.cs u') Y.hK hN q)
  have e2 := Equiv.ofBijective _ (Formalism.L2.SG.Pf.Act.gamL_levi_bij (Y.cs u') Y.TR Y.hK hN q)
  exact Finite.of_equiv _ (e2.symm.trans e1)

theorem fib_bij (hN : Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u' Y.hK) (s₀ : Formalism.L2.SG.PackageTie2.TT Y u u') :
    ∃ f : {s : Formalism.L2.SG.PackageTie2.TT Y u u' // s.toTerm = s₀.toTerm} → autLz D (X.Fu u') s₀.lam', Function.Bijective f := by
  haveI := autLz_finite hN s₀.mem'
  have hex : ∀ s : {s : Formalism.L2.SG.PackageTie2.TT Y u u' // s.toTerm = s₀.toTerm}, ∃ c : (VS D).V ≃ₗ[D.host.E] (VS D).V,
      c ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧ Formalism.HermitianLatticesTheory.gmap c s₀.lam' = s₀.lam' ∧
      (∀ a, c ((X.Fu u').fvec a) = (X.Fu u').fvec a) ∧
      ∃ n ∈ NLam s₀.lam (lf D (X.Fu u)), ∃ ν ∈ NLam s₀.lam' (lf D (X.Fu u')),
        (s : Formalism.L2.SG.PackageTie2.TT Y u u').lin = n * s₀.lin * ν * c :=
    fun s => fib_c s.2.symm
  let cf : {s : Formalism.L2.SG.PackageTie2.TT Y u u' // s.toTerm = s₀.toTerm} → (VS D).V ≃ₗ[D.host.E] (VS D).V := fun s => (hex s).choose
  have hcf : ∀ s, _ := fun s => (hex s).choose_spec
  let f : {s : Formalism.L2.SG.PackageTie2.TT Y u u' // s.toTerm = s₀.toTerm} → autLz D (X.Fu u') s₀.lam' := fun s =>
    ⟨indQ (X.Fu u') (cf s) (hcf s).1 (hcf s).2.2.1, indQ_mem (X.Fu u') _ _ _ (hcf s).2.1⟩
  refine ⟨f, fun s s' hss => ?_, fun φ => ?_⟩
  · have hq := sub_mem_of_indQ (X.Fu u') (hcf s).1 (hcf s).2.2.1 (hcf s').1 (hcf s').2.2.1
      (congrArg Subtype.val hss)
    obtain ⟨n, hn, ν, hν, he⟩ := (hcf s).2.2.2
    obtain ⟨n', hn', ν', hν', he'⟩ := (hcf s').2.2.2
    exact Subtype.ext (eq_of_dec s.2.symm s'.2.symm hn hn' hν hν' (hcf s).1 (hcf s').1 (hcf s).2.1 (hcf s').2.1
      (hcf s).2.2.1 (hcf s').2.2.1 he he' hq)
  · obtain ⟨φ, hφ⟩ := φ
    obtain ⟨g, hg⟩ := (Formalism.L2.SG.Pf.Act.gamL_autLz_bij (Y.cs u') Y.hK hN ⟨s₀.lam', s₀.mem'⟩).2 ⟨φ, hφ⟩
    have hc₁s : Formalism.L2.SG.Pf.Act.isoG g.1 ∈ stabF D (X.Fu u') := Formalism.L2.SG.Pf.Act.isoG_stab g.1
    have hc₁ : Formalism.L2.SG.Pf.Act.isoG g.1 ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := hc₁s.1
    have hc₁fix : ∀ a, Formalism.L2.SG.Pf.Act.isoG g.1 ((X.Fu u').fvec a) = (X.Fu u').fvec a := by
      intro a
      refine Fin.lastCases ?_ (fun i => ?_) a
      · have hz : (X.Fu u').z = X.zu u' := X.flagZVector u'
        simp only [FlagG.fvec, Fin.snoc_last]
        rw [hz]
        exact Formalism.L2.SG.Pf.Act.isoG_fix g.1 _ (Or.inr rfl)
      · have he : (X.Fu u').e i = X.eX i := congrFun (X.Fu_e u') i
        simp only [FlagG.fvec, Fin.snoc_castSucc]
        rw [he]
        exact Formalism.L2.SG.Pf.Act.isoG_e g.1 i
    have hc₁g : Formalism.HermitianLatticesTheory.gmap (Formalism.L2.SG.Pf.Act.isoG g.1) s₀.lam' = s₀.lam' :=
      Formalism.L2.SG.Pf.Act.isoG_lat (Y.cs u') ⟨s₀.lam', s₀.mem'⟩ g
    have hφ' : ⇑(Formalism.L2.SG.Pf.Act.indW (Formalism.L2.SG.Pf.Act.isoG g.1) hc₁s) = φ := congrArg Subtype.val hg
    set c₁ := Formalism.L2.SG.Pf.Act.isoG g.1 with hc₁def
    have hA₁ : IsAutLam (VS D) s₀.lam' c₁ := ⟨hc₁, hc₁g⟩
    obtain ⟨x, hx⟩ := Formalism.L2.SG.Pf.ratPt_holds D X c₁⁻¹ (Subgroup.inv_mem _ hc₁)
    have hβ : c₁⁻¹ ∈ Formalism.L2.SG.Saturated.AutF s₀.lam' (lf D (X.Fu u')) := by
      refine ⟨Formalism.L2.SG.Pf.isAutLam_inv hA₁, fun a => inv_fix (X.Fu u') hc₁fix a, ?_⟩
      have := inv_fix (X.Fu u') hc₁fix (Fin.last _)
      simpa [FlagG.fvec] using this
    set s₁ := Formalism.L2.SG.Pf.SatGramActR.tmap x c₁⁻¹ Formalism.L2.SG.Pf.SatGramActR.autFConjN_holds hx s₀ with hs₁
    have ht : s₁.toTerm = s₀.toTerm := Formalism.L2.SG.Pf.SatGramActR.toTerm_tmap _ _ _ hx s₀
    have hcls := Formalism.L2.SG.Pf.SatGramActR.tmap_cls x c₁⁻¹ Formalism.L2.SG.Pf.SatGramActR.autFConjN_holds hx s₀ hβ
    obtain ⟨n₁, hn₁, n₁', hn₁', hlin⟩ := lin_of_cls s₁ _ hcls
    have hν₁ : c₁ * n₁' * c₁⁻¹ ∈ NLam s₀.lam' (lf D (X.Fu u')) :=
      Formalism.L2.SG.Pf.nlam_conj hA₁ (fun a => (hc₁fix a).symm) hn₁'
    have hlin' : s₁.lin = n₁ * s₀.lin * (c₁ * n₁' * c₁⁻¹) * c₁ := by
      rw [hlin]
      show n₁ * (s₀.lin * c₁⁻¹⁻¹) * n₁' = _
      group
    refine ⟨⟨s₁, ht⟩, Subtype.ext ?_⟩
    obtain ⟨n, hn, ν, hν, he⟩ := (hcf ⟨s₁, ht⟩).2.2.2
    have hwd := wd (F := X.Fu u) hn hn₁ hν hν₁ (hcf ⟨s₁, ht⟩).1 hc₁ (hcf ⟨s₁, ht⟩).2.1 hc₁g
      (hcf ⟨s₁, ht⟩).2.2.1 hc₁fix (he.symm.trans hlin')
    show indQ (X.Fu u') (cf ⟨s₁, ht⟩) (hcf ⟨s₁, ht⟩).1 (hcf ⟨s₁, ht⟩).2.2.1 = φ
    rw [← hφ']
    funext w
    induction w using Submodule.Quotient.induction_on with
    | H y =>
      rw [indQ_mk, Formalism.L2.SG.Pf.Act.indW_mk, Submodule.Quotient.eq]
      exact hwd y y.2

theorem liftMassC_of (hN : Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u' Y.hK) : Formalism.L2.SG.Pf.RowForm.LiftMassC X Y u u' := by
  intro t _
  obtain ⟨s₀, hs₀⟩ := Formalism.L2.SG.Pf.Act.liftOnto (Formalism.L2.SG.Pf.WittFlags.LatIso_holds D)
    (fun n hn => Formalism.L2.SG.Pf.ratPt_holds D X n hn) Y u u'
    (Formalism.L2.SG.Pf.toTermRel_holds X u u' (X.Fu u) (X.Fu u')) t
  subst hs₀
  haveI := autLz_finite hN s₀.mem'
  obtain ⟨f, hf⟩ := fib_bij hN s₀
  let e := Equiv.ofBijective f hf
  haveI : Finite {s : Formalism.L2.SG.PackageTie2.TT Y u u' // s.toTerm = s₀.toTerm} := Finite.of_equiv _ e.symm
  haveI : Fintype {s : Formalism.L2.SG.PackageTie2.TT Y u u' // s.toTerm = s₀.toTerm} := Fintype.ofFinite _
  have hw : ∀ s : {s : Formalism.L2.SG.PackageTie2.TT Y u u' // s.toTerm = s₀.toTerm},
      Formalism.MainNotions.S.wRow D (X.Fu u') s.1.lam' = Formalism.MainNotions.S.wRow D (X.Fu u') s₀.lam' := fun s => by
    rw [lam'_eq s.2.symm]
  have hpos : 0 < Nat.card (autLz D (X.Fu u') s₀.lam') := by
    haveI : Nonempty (autLz D (X.Fu u') s₀.lam') := ⟨f ⟨s₀, rfl⟩⟩
    exact Nat.card_pos
  show ∑' s : {s : Formalism.L2.SG.PackageTie2.TT Y u u' // s.toTerm = s₀.toTerm}, Formalism.MainNotions.S.wRow D (X.Fu u') s.1.lam' = 1
  rw [tsum_fintype, Finset.sum_congr rfl (fun s _ => hw s), Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  unfold Formalism.MainNotions.S.wRow
  rw [← Nat.card_eq_fintype_card, Nat.card_congr e]
  exact mul_inv_cancel₀ (by exact_mod_cast hpos.ne')

end Count

end Formalism.L2.SG.Pf.FibreCounting
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ToTermAct
section
attribute [-instance] PI.WSF.instMeasurableSpaceMat PI.WSF.instBorelSpaceMat
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.PackageTie2 Formalism.L2.SG.NormCut Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Pf.unitaryCongruence

namespace Formalism.L2.SG.Pf.KernelOfEmbedding

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Act

variable {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word}

theorem eq_isoG {g : Gam X u'} {β : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hx : RatLink X (g : X.B.I.GA) β) :
    β = Formalism.L2.SG.Pf.Act.isoG g := by
  apply LinearEquiv.ext
  intro y
  apply Formalism.L2.SG.Pf.Act.inclCrd_inj
  rw [Formalism.L2.SG.Pf.Act.isoG_spec, ← Formalism.L2.SG.Pf.LatDictK.ratLink_incl X hx y]

theorem kB_mem (q : {Λ // Λ ∈ Y.what₂ u'}) (γ : Formalism.L2.SG.Pf.Act.GamL (Y.cs u') q) :
    Formalism.L2.SG.Pf.SatGramActL.kB (Y.cs u') q.1 γ.1 ∈ X.B.I.Kset := by
  unfold Formalism.L2.SG.Pf.SatGramActL.kB
  rw [Formalism.L2.SG.Pf.Act.aK_eq]
  exact γ.2


variable (Y) in
theorem isoG_lift (q : {Λ // Λ ∈ Y.what₂ u'}) (γ : Formalism.L2.SG.Pf.Act.GamL (Y.cs u') q) :
    RatLink X (γ.1 : X.B.I.GA) (Formalism.L2.SG.Pf.Act.isoG γ.1) ∧
      Formalism.L2.SG.Pf.Act.isoG γ.1 ∈ Formalism.L2.SG.Saturated.AutF q.1 (lf D (X.Fu u')) := by
  obtain ⟨β, hx, hβ⟩ :=
    Formalism.L2.SG.Pf.SatGramActL.betaLift_holds D X u' (Y.what₂ u') (Y.cs u') q.1 q.2 γ.1 (kB_mem q γ)
  have e := eq_isoG hx
  subst e
  exact ⟨hx, hβ⟩


variable (Y) in
def act (q : {Λ // Λ ∈ Y.what₂ u'}) (γ : Formalism.L2.SG.Pf.Act.GamL (Y.cs u') q) (t : Formalism.L2.SG.PackageTie2.TT Y u u') : Formalism.L2.SG.PackageTie2.TT Y u u' :=
  Formalism.L2.SG.Pf.SatGramActR.tmap (γ.1 : X.B.I.GA) (Formalism.L2.SG.Pf.Act.isoG γ.1)
    Formalism.L2.SG.Pf.SatGramActR.autFConjN_holds (isoG_lift Y q γ).1 t

theorem toTerm_act (q : {Λ // Λ ∈ Y.what₂ u'}) (γ : Formalism.L2.SG.Pf.Act.GamL (Y.cs u') q) (t : Formalism.L2.SG.PackageTie2.TT Y u u') :
    (act Y q γ t).toTerm = t.toTerm :=
  Formalism.L2.SG.Pf.SatGramActR.toTerm_tmap _ _ _ _ t

theorem iota_act (hIR : Formalism.L2.SG.Pf.SatGramRep.IotaRepC) (q : {Λ // Λ ∈ Y.what₂ u'})
    (γ : Formalism.L2.SG.Pf.Act.GamL (Y.cs u') q) (t : Formalism.L2.SG.PackageTie2.TT Y u u') (ht : t.lam' = q.1) :
    iotaOf Y.TR (Y.cs u) (Y.cs u') (act Y q γ t) =
      iotaOf Y.TR (Y.cs u) (Y.cs u') t * (levi Y.TR (Formalism.L2.SG.Pf.SatGramActL.kB (Y.cs u') q.1 γ.1))⁻¹ := by
  have hβt : Formalism.L2.SG.Pf.Act.isoG γ.1 ∈ Formalism.L2.SG.Saturated.AutF t.lam' (lf D (X.Fu u')) := by
    rw [ht]; exact (isoG_lift Y q γ).2
  have hkt : Formalism.L2.SG.Pf.SatGramActL.kB (Y.cs u') t.lam' γ.1 ∈ X.B.I.Kset := by
    rw [ht]; exact kB_mem q γ
  unfold act
  rw [Formalism.L2.SG.Pf.SatGramRep.iotaOf_of_mk (hIR D X Y u u') (Formalism.L2.SG.Pf.SatGramActR.tmap (γ.1 : X.B.I.GA) (Formalism.L2.SG.Pf.Act.isoG γ.1) Formalism.L2.SG.Pf.SatGramActR.autFConjN_holds (isoG_lift Y q γ).1 t)
    (Formalism.L2.SG.Pf.SatGramActR.rmul (γ.1 : X.B.I.GA) _ (isoG_lift Y q γ).1 hβt t.rep)
    (Formalism.L2.SG.Pf.SatGramActR.tmap_cls _ _ _ _ t hβt)]
  rw [Formalism.L2.SG.Pf.SatGramRep.iotaOf_of_mk (hIR D X Y u u') t t.rep (Quot.out_eq t.cls).symm]
  have e2 : ((((Y.cs u').h ((Y.cs u').base t.lam') : X.B.I.Gf) * X.xu u')⁻¹ * ((γ.1 : X.B.I.GA)⁻¹).2 *
      (((Y.cs u').h ((Y.cs u').base t.lam') : X.B.I.Gf) * X.xu u')) =
      (Formalism.L2.SG.Pf.SatGramActL.kB (Y.cs u') t.lam' γ.1)⁻¹ := by
    have eg : (γ.1 : X.B.I.GA).2 = (iotaF X u' γ.1 : X.B.I.Gf) := rfl
    rw [Prod.snd_inv, eg]
    unfold Formalism.L2.SG.Pf.SatGramActL.kB
    group
  have hG1 : Good X (kOf X u u' ((Y.cs u).h ((Y.cs u).base t.lam) : X.B.I.Gf)
      ((Y.cs u').h ((Y.cs u').base t.lam') : X.B.I.Gf) t.rep.1.1) :=
    Formalism.L2.SG.Closed.AdmPar_holds (Y.cs u) (Y.cs u') (Formalism.L2.SG.Full.Full.frameTie (X := X) u u') t
  have hG2 : Good X (Formalism.L2.SG.Pf.SatGramActL.kB (Y.cs u') t.lam' γ.1) :=
    Formalism.L2.SG.Pf.SatGramActL.satGramActLIota_kB_good (Y.cs u') t.lam' γ.1 hkt
  show levi Y.TR (kOf X u u' ((Y.cs u).h ((Y.cs u).base t.lam) : X.B.I.Gf)
      ((Y.cs u').h ((Y.cs u').base t.lam') : X.B.I.Gf) (t.rep.1.1 * (γ.1 : X.B.I.GA)⁻¹)) = _
  rw [Formalism.L2.SG.Pf.SatGramActR.kOf_mul_right, e2, levi_mul Y.TR hG1 (good_inv X hG2), levi_inv Y.TR hG2]
  have hq2 : Formalism.L2.SG.Pf.SatGramActL.kB (Y.cs u') t.lam' γ.1 = Formalism.L2.SG.Pf.SatGramActL.kB (Y.cs u') q.1 γ.1 := by
    rw [ht]
  rw [hq2]

theorem amp_act (hB : Formalism.L2.SG.Pf.SatGramActL.ChiNBiAll) (hAR : Formalism.L2.SG.Pf.SatGramRep.AmpRepNC)
    (hOI : OOIntAll X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) (q : {Λ // Λ ∈ Y.what₂ u'})
    (γ : Formalism.L2.SG.Pf.Act.GamL (Y.cs u') q) (t : Formalism.L2.SG.PackageTie2.TT Y u u') (ht : t.lam' = q.1) :
    amp Y (act Y q γ t) = (amp Y t).comp (X.piU u' ((γ.1 : X.B.I.GA).1)⁻¹) := by
  have hβt : Formalism.L2.SG.Pf.Act.isoG γ.1 ∈ Formalism.L2.SG.Saturated.AutF t.lam' (lf D (X.Fu u')) := by
    rw [ht]; exact (isoG_lift Y q γ).2
  have hkt : Formalism.L2.SG.Pf.SatGramActL.kB (Y.cs u') t.lam' γ.1 ∈ X.B.I.Kset := by
    rw [ht]; exact kB_mem q γ
  have hF := Formalism.L2.SG.Pf.fundExistsC_holds D X Y u u'
  have hft := Formalism.L2.SG.Pf.SatGramActL.fundOf_spec hF t
  have hΩ : IsSFund X.B.I (ROset X (X.Fu u) (X.Fu u') t.lam t.lam'
      (Formalism.L2.SG.Pf.SatGramActR.rmul (γ.1 : X.B.I.GA) _ (isoG_lift Y q γ).1 hβt t.rep).1.2) (FundOf t) := by
    have e := Formalism.L2.SG.Pf.SatGramActR.roset_mul_aut (X := X) (F0 := X.Fu u) (Λ := t.lam) hβt t.rep.1.2
    convert hft using 2
    exact e
  show ampN (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') (act Y q γ t) =
    (ampN (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') t).comp (X.piU u' ((γ.1 : X.B.I.GA).1)⁻¹)
  unfold act
  rw [Formalism.L2.SG.Pf.SatGramRep.ampN_of_mk (Y.FN u) (Y.FN u') (hAR D X Y u u') hF hOI (Formalism.L2.SG.Pf.SatGramActR.tmap (γ.1 : X.B.I.GA) (Formalism.L2.SG.Pf.Act.isoG γ.1) Formalism.L2.SG.Pf.SatGramActR.autFConjN_holds (isoG_lift Y q γ).1 t)
    (Formalism.L2.SG.Pf.SatGramActR.rmul (γ.1 : X.B.I.GA) _ (isoG_lift Y q γ).1 hβt t.rep)
    (Formalism.L2.SG.Pf.SatGramActR.tmap_cls _ _ _ _ t hβt) (FundOf t) hΩ]
  rw [Formalism.L2.SG.Pf.SatGramRep.ampN_of_mk (Y.FN u) (Y.FN u') (hAR D X Y u u') hF hOI t t.rep
    (Quot.out_eq t.cls).symm (FundOf t) hft]
  have e2 : ((((Y.cs u').h ((Y.cs u').base t.lam') : X.B.I.Gf) * X.xu u')⁻¹ * ((γ.1 : X.B.I.GA)⁻¹).2 *
      (((Y.cs u').h ((Y.cs u').base t.lam') : X.B.I.Gf) * X.xu u')) =
      (Formalism.L2.SG.Pf.SatGramActL.kB (Y.cs u') t.lam' γ.1)⁻¹ := by
    have eg : (γ.1 : X.B.I.GA).2 = (iotaF X u' γ.1 : X.B.I.Gf) := rfl
    rw [Prod.snd_inv, eg]
    unfold Formalism.L2.SG.Pf.SatGramActL.kB
    group
  have hκ := Formalism.L2.SG.Pf.SatGramActL.ChiLeft.kBB_mem Y u u' t.mem t.mem' t.rep
  have eχ : chiN X (kOf X u u' ((Y.cs u).h ((Y.cs u).base t.lam) : X.B.I.Gf)
      ((Y.cs u').h ((Y.cs u').base t.lam') : X.B.I.Gf) (t.rep.1.1 * (γ.1 : X.B.I.GA)⁻¹)) =
      chiN X (kOf X u u' ((Y.cs u).h ((Y.cs u).base t.lam) : X.B.I.Gf)
        ((Y.cs u').h ((Y.cs u').base t.lam') : X.B.I.Gf) t.rep.1.1) := by
    rw [Formalism.L2.SG.Pf.SatGramActR.kOf_mul_right, e2]
    exact Formalism.L2.SG.Pf.SatGramActR.chiNR_holds hB D X u' ((Y.cs u').h ((Y.cs u').base t.lam')) γ.1 _ hκ hkt
  show ((scl (Y.FN u) (Y.FN u') (X := X) (u := u) (u' := u') * X.volK2 : ℝ) : ℂ) •
      (chiN X (kOf X u u' ((Y.cs u).h ((Y.cs u).base t.lam) : X.B.I.Gf)
        ((Y.cs u').h ((Y.cs u').base t.lam') : X.B.I.Gf) (t.rep.1.1 * (γ.1 : X.B.I.GA)⁻¹)) •
        (haveI := FiniteDimensional.complete ℂ (X.Vpi u)
         OO (Formalism.L2.SG.ProjRows.muInf X.B.I) (FundOf t) (X.Wu u) (X.Wu u')
          (t.rep.1.1.1 * ((γ.1 : X.B.I.GA).1)⁻¹))) = _
  rw [eχ, Formalism.L2.SG.Pf.SatGramActR.ooR_holds D X u u' γ.1 (FundOf t) t.rep.1.1.1]
  rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.smul_comp]

theorem fib_gam (hN : Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u' Y.hK) {s s' : Formalism.L2.SG.PackageTie2.TT Y u u'} (h : s.toTerm = s'.toTerm) :
    ∃ γ : Formalism.L2.SG.Pf.Act.GamL (Y.cs u') ⟨s.lam', s.mem'⟩, s' = act Y ⟨s.lam', s.mem'⟩ γ s := by
  obtain ⟨c, hc, hg, hfix, n, hn, ν, hν, he⟩ := Formalism.L2.SG.Pf.FibreCounting.fib_c h
  have hst := Formalism.L2.SG.Pf.FibreCounting.stabF_of_fix (X.Fu u') hc hfix
  obtain ⟨g, hgq⟩ := (Formalism.L2.SG.Pf.Act.gamL_autLz_bij (Y.cs u') Y.hK hN ⟨s.lam', s.mem'⟩).2
    ⟨Formalism.L2.SG.Pf.Act.indW c hst, Formalism.L2.SG.Pf.Act.indW_mem s.lam' c hst hg⟩
  have hW : (Formalism.L2.SG.Pf.Act.indW (Formalism.L2.SG.Pf.Act.isoG g.1) (Formalism.L2.SG.Pf.Act.isoG_stab g.1) :
      Formalism.MainNotions.S.WbQ D (X.Fu u') → Formalism.MainNotions.S.WbQ D (X.Fu u')) = Formalism.L2.SG.Pf.Act.indW c hst :=
    congrArg Subtype.val hgq
  have hq : ∀ y ∈ perpS (VS D) (X.Fu u').X, c y - Formalism.L2.SG.Pf.Act.isoG g.1 y ∈ (X.Fu u').X := by
    intro y hy
    have e := congrFun hW.symm (Submodule.Quotient.mk ⟨y, hy⟩)
    rw [Formalism.L2.SG.Pf.Act.indW_mk, Formalism.L2.SG.Pf.Act.indW_mk, Submodule.Quotient.eq] at e
    simpa using e
  have hfixg : ∀ a, Formalism.L2.SG.Pf.Act.isoG g.1 ((X.Fu u').fvec a) = (X.Fu u').fvec a := by
    intro a
    refine Fin.lastCases ?_ (fun i => ?_) a
    · simp only [FlagG.fvec, Fin.snoc_last]
      rw [X.flagZVector u']
      exact Formalism.L2.SG.Pf.Act.isoG_fix g.1 _ (Or.inr rfl)
    · simp only [FlagG.fvec, Fin.snoc_castSucc]
      rw [X.Fu_e u']
      exact Formalism.L2.SG.Pf.Act.isoG_e g.1 i
  have hA : IsAutLam (VS D) s.lam' c := ⟨hc, hg⟩
  have hA' : IsAutLam (VS D) s.lam' (Formalism.L2.SG.Pf.Act.isoG g.1) :=
    ⟨(Formalism.L2.SG.Pf.Act.isoG_stab g.1).1, Formalism.L2.SG.Pf.Act.isoG_lat (Y.cs u') ⟨s.lam', s.mem'⟩ g⟩
  have hm := Formalism.L2.SG.Pf.FibreCounting.nlam_of_sub (X.Fu u') hA hA' hfix hfixg hq

  have hkinv : colD ((Y.cs u').h ((Y.cs u').base s.lam')) (iotaF X u' g.1⁻¹ * (Y.cs u').h ((Y.cs u').base s.lam'))
      ∈ X.B.I.Kset := by
    rw [← Formalism.L2.SG.Pf.Act.aK_eq]
    have h1 := K_inv X.B.I (kB_mem (Y := Y) ⟨s.lam', s.mem'⟩ g)
    unfold Formalism.L2.SG.Pf.SatGramActL.kB at h1
    rw [map_inv]
    convert h1 using 1
    push_cast
    group
  let γ : Formalism.L2.SG.Pf.Act.GamL (Y.cs u') ⟨s.lam', s.mem'⟩ := ⟨g.1⁻¹, hkinv⟩
  have hxg := (isoG_lift Y ⟨s.lam', s.mem'⟩ g).1
  have hxi : RatLink X (γ.1 : X.B.I.GA) (Formalism.L2.SG.Pf.Act.isoG g.1)⁻¹ := by
    have := Formalism.L2.SG.Pf.ratLink_inv X hxg
    simpa [γ] using this
  have hiso : Formalism.L2.SG.Pf.Act.isoG γ.1 = (Formalism.L2.SG.Pf.Act.isoG g.1)⁻¹ := (eq_isoG hxi).symm
  refine ⟨γ, ?_⟩
  have hl : s.lam = s'.lam := (Formalism.L2.SG.Pf.FibreCounting.fib_dec h).1
  have hl' : s.lam' = s'.lam' := Formalism.L2.SG.Pf.FibreCounting.lam'_eq h
  have hβt : Formalism.L2.SG.Pf.Act.isoG γ.1 ∈ Formalism.L2.SG.Saturated.AutF s.lam' (lf D (X.Fu u')) :=
    (isoG_lift Y ⟨s.lam', s.mem'⟩ γ).2
  have hcls := Formalism.L2.SG.Pf.SatGramActR.tmap_cls (γ.1 : X.B.I.GA) (Formalism.L2.SG.Pf.Act.isoG γ.1)
    Formalism.L2.SG.Pf.SatGramActR.autFConjN_holds (isoG_lift Y ⟨s.lam', s.mem'⟩ γ).1 s hβt

  set G := Formalism.L2.SG.Pf.Act.isoG g.1 with hG
  have hGA : G⁻¹ ∈ Formalism.L2.SG.Saturated.AutF s.lam' (lf D (X.Fu u')) := by rw [← hiso]; exact hβt
  have hν2 : G⁻¹ * ν * G⁻¹⁻¹ ∈ NLam s.lam' (lf D (X.Fu u')) :=
    Formalism.L2.SG.Pf.SatGramActL.nlam_conj hGA hν
  have hν3 : (G⁻¹ * ν * G⁻¹⁻¹) * (c⁻¹ * G)⁻¹ ∈ NLam s.lam' (lf D (X.Fu u')) :=
    Formalism.L2.SG.Pf.nlamPf_mul hν2 (Formalism.L2.SG.Pf.nlamPf_inv hm)
  rcases s' with ⟨k, hk, k', hk', q'⟩
  simp only at hl hl' he
  subst hl hl'
  show (⟨s.lam, hk, s.lam', hk', q'⟩ : Formalism.L2.SG.PackageTie2.TT Y u u') =
    ⟨s.lam, s.mem, s.lam', s.mem', (Formalism.L2.SG.Pf.SatGramActR.tmap (γ.1 : X.B.I.GA) (Formalism.L2.SG.Pf.Act.isoG γ.1)
      Formalism.L2.SG.Pf.SatGramActR.autFConjN_holds (isoG_lift Y ⟨s.lam', s.mem'⟩ γ).1 s).cls⟩
  rw [hcls]
  congr 1
  rw [← Quot.out_eq q']
  refine (Quot.sound ⟨n, hn, (G⁻¹ * ν * G⁻¹⁻¹) * (c⁻¹ * G)⁻¹, hν3, ?_⟩).symm
  show GTerm.lin (⟨s.lam, hk, s.lam', hk', q'⟩ : Formalism.L2.SG.PackageTie2.TT Y u u') =
    n * (GTerm.lin s * (Formalism.L2.SG.Pf.Act.isoG γ.1)⁻¹) * ((G⁻¹ * ν * G⁻¹⁻¹) * (c⁻¹ * G)⁻¹)
  rw [he, hiso]
  group

end Act

end Formalism.L2.SG.Pf.KernelOfEmbedding
end
end

