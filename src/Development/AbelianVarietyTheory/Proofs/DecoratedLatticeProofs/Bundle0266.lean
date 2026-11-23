module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0296
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameActionMulEquivFiniteAdelicUnitary
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0334
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0315
public import Formalism.LocalToGlobal.GlobalTheory.GL6.PSplitT
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ColDictPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.STiesR
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0261
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftsAllChartsEqClassSum
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0069
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0180
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0262
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RtrMemOfNorm
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MiTop.CenIsom

variable {D : D7} {X : HidaSetting D} {u : D.what₂.Word}

theorem rtr_mem_of_norm (hK : X.LevelSubgroupCharacter) {δ : Hfin X u}
    (hn : ∀ κ : Ku X u hK, ∃ κ' : Ku X u hK, (κ : Hfin X u) * δ = δ * κ' ∧
      ((psiK X u hK κ' : ℂˣ) : ℂ) = ((psiK X u hK κ : ℂˣ) : ℂ))
    {T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)} (hT : T ∈ Cu X u hK) : rtr X δ T ∈ Cu X u hK := by
  obtain ⟨h1, h2⟩ := hT
  refine ⟨fun ξ => ⟨fun γ y => ?_, fun y κ => ?_⟩, fun g ξ y => ?_⟩
  · show T ξ ((_, _) * y * (1, δ)) = T ξ (y * (1, δ))
    rw [mul_assoc]
    exact (h1 ξ).1 γ _
  · obtain ⟨κ', hκ', hψ⟩ := hn κ
    have hc : ((1 : Hinf X u), (κ : Hfin X u)) * (1, δ) = (1, δ) * (1, (κ' : Hfin X u)) :=
      Prod.ext rfl hκ'
    have e : y * (1, (κ : Hfin X u)) * (1, δ) = y * (1, δ) * (1, (κ' : Hfin X u)) := by
      rw [mul_assoc, mul_assoc, hc]
    refine (congrArg (T ξ) e).trans (((h1 ξ).2 _ κ').trans ?_)
    rw [hψ]
    rfl
  · have hc : ((g : Hinf X u), (1 : Hfin X u)) * (1, δ) = (1, δ) * (g, 1) :=
      Prod.ext ((mul_one g).trans (one_mul g).symm) ((one_mul δ).trans (mul_one δ).symm)
    have e : y * (g, 1) * (1, δ) = y * (1, δ) * (g, 1) := by
      rw [mul_assoc, mul_assoc, hc]
    exact (h2 g ξ (y * (1, δ))).trans (congrArg (T ξ) e.symm)

theorem rtr_comm {δ δ' : Hfin X u} (h : δ * δ' = δ' * δ) (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) :
    rtr X δ' (rtr X δ T) = rtr X δ (rtr X δ' T) := by
  ext ξ y
  have hc : ((1 : Hinf X u), δ') * (1, δ) = (1, δ) * (1, δ') := Prod.ext rfl h.symm
  have e : y * (1, δ') * (1, δ) = y * (1, δ) * (1, δ') := by rw [mul_assoc, mul_assoc, hc]
  exact congrArg (T ξ) e


set_option maxHeartbeats 3000000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem exists_rtr_dia {F : Formalism.L2.Forms.Forms0 D u} (Tr : Transport X u F) (hK : X.LevelSubgroupCharacter) (hL : LevelMatch X Tr hK)
    (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ) :
    ∃ δ : Hfin X u, ∀ T ∈ Cu X u hK, rtr X δ T ∈ Cu X u hK ∧
      dictA X Tr (rtr X δ T) = (D.mem u).A.rhoT v a (dictA X Tr T) := by
  have hW : WittX X u Tr.wt := ⟨Tr.wt_isom, Tr.wt_e, Tr.wt_f, Tr.weight_z⟩
  have hA : IsAdeleIso X Tr.ιA := ⟨Tr.ιA_rat, Tr.ιA_int⟩
  have hσ := GlobalTheory.St.G.IotaSigmaCompatibility.iotaA_sigA D X Tr.ιA hA
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.frame_action_mulEquiv D X u Tr.wt Tr.ιA hW hA hσ
  obtain ⟨-, hΓ, hsT⟩ := GlobalTheory.transport_rational_points D X u Tr.wt Tr.ιA hW hA Φ hΦ
  obtain ⟨hψ, -, hφ, -, -⟩ := cols_sharp_dictionary D X u hK
  obtain ⟨k, hk, hkT⟩ := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.unit_lift_int_prime_field (D.mem u).A.T_prime ((D.mem u).A.card_Fv v) a
  obtain ⟨e, he, hee, hσe⟩ := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.splitAtT_of_tied F.atT v
  obtain ⟨y, hy⟩ := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.is_diamond_of_local_diamond F.cls0.lev (F.atT.eV v).1 (F.atT.eV v).2 k
    (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.local_diamond_of_split_idempotent F.cls0.lev _ _ (D.mem u).A.T_prime k hkT e he hee hσe)
  have hlev := fun h => hL.2 h (Φ h) ((hΦ h (Φ h)).2 rfl)
  obtain ⟨δ, hδ⟩ : ∃ δ : Hfin X u, Φ δ = Tr.h0 * y * Tr.h0⁻¹ := Φ.surjective _
  refine ⟨δ, fun T hT => ⟨rtr_mem_of_norm hK (fun κ => ?_) hT, ?_⟩⟩
  · have hκ := (hlev κ).1.1 κ.2
    have hm := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.diamond_conj_mem_level F.cls0.lev _ _ hy ⟨_, hκ⟩
    have hχ := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.level_character_conj_diamond F.cls0.lev _ _ (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.level_places_not_bad F.atT v) hy ⟨_, hκ⟩
    have e1 : Tr.h0⁻¹ * Φ (δ⁻¹ * κ * δ) * Tr.h0 = y⁻¹ * (Tr.h0⁻¹ * Φ κ * Tr.h0) * y := by
      rw [map_mul, map_mul, map_inv, hδ]
      group
    have e2 := congrArg Subtype.val e1
    have hm' : (Tr.h0⁻¹ * Φ (δ⁻¹ * κ * δ) * Tr.h0).1 ∈ F.cls0.lev.U := by
      rw [e2]
      exact hm
    have hin := (hlev (δ⁻¹ * κ * δ)).1.2 hm'
    refine ⟨⟨δ⁻¹ * κ * δ, hin⟩, by simp only [← mul_assoc, mul_inv_cancel, one_mul], ?_⟩
    rw [(hlev _).2 hin hm', (hlev κ).2 κ.2 hκ, ← hχ]
    exact congrArg (fun x => ((F.cls0.lev.chi x : ℂˣ) : ℂ)) (Subtype.ext e2)
  · have key := GlobalTheory.adForms_of_equivariant D.host.F D.host.E (Formalism.L2.Forms.sigD D) (D.R.N 0)
      (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) _ _ _ F.cls0.lev (Gam X u) (Hinf X u) (Hfin X u)
      (iotaI X u) (iotaF X u) (Ku X u hK) (psiK X u hK) Φ Tr.h0 D.what₂.Tau (Formalism.L2.Forms.embT D)
      ((D.fm u).lam 0) (X.Vpi u) (piRep X u) Tr.J hψ
      (fun h => (hlev h).1) (fun h hk hy => (hlev h).2 hk hy) hΓ
      (fun γ g hγ ξ y y' hy => Tr.J_eqv _ (iotaI X u γ).2 ξ y y' (by rw [hsT γ g hγ]; exact hy))
      (fun ξ => by rw [← Formalism.L2.Forms.lamT_zero]; exact Tr.J_val ξ)
      (shP X u T) (hφ ⟨T, hT⟩)
    have hc : ∀ c, Φ (Tr.hc c) = F.cls0.y c * Tr.h0⁻¹ := fun c => (hΦ (Tr.hc c) _).1 (Tr.hc_rep c)
    have e1 : dictA X Tr T = fun c s =>
        (fun x => Tr.J (shP X u T (Φ.symm (x * Tr.h0⁻¹)))) (F.cls0.y c) (F.val0.eY s) := by
      funext c s
      show Tr.J (shP X u T (Tr.hc c)) (F.val0.eY s) = Tr.J (shP X u T (Φ.symm (F.cls0.y c * Tr.h0⁻¹))) (F.val0.eY s)
      rw [← hc, MulEquiv.symm_apply_apply]
    rw [e1, Formalism.L2.Forms.rhoT_eq F.val0 v a k hk y hy _ key.1]
    funext c s
    have e2 : Tr.hc c * δ = Φ.symm (F.cls0.y c * y * Tr.h0⁻¹) := by
      apply Φ.injective
      rw [map_mul, MulEquiv.apply_symm_apply, hc, hδ]
      group
    show Tr.J (shP X u (rtr X δ T) (Tr.hc c)) (F.val0.eY s) =
      Tr.J (shP X u T (Φ.symm (F.cls0.y c * y * Tr.h0⁻¹))) (F.val0.eY s)
    rw [Formalism.L2.SG.Pf.ColDictPf.rieszVector_rightTranslate, e2]

theorem ram_rtr {F : Formalism.L2.Forms.Forms0 D u} (Tr : Transport X u F) (hK : X.LevelSubgroupCharacter) (hL : LevelMatch X Tr hK)
    (hI : ColDictInto X Tr hK) (hB : ColDictBij X Tr hK) (δ : Hfin X u) (hδ : ∀ k : Hfin X u, δ * k = k * δ)
    (T S : Cu X u hK) (hS : S.1 = rtr X δ T.1) (hT : colDictL X Tr hK T ∈ (D.mem u).A.Mram) :
    colDictL X Tr hK S ∈ (D.mem u).A.Mram := by
  refine ⟨hI S, (Submodule.mem_iInf _).2 fun v => ?_⟩
  have h0 : (D.mem u).A.Nm v (dictA X Tr T.1) = 0 := (Submodule.mem_iInf _).1 hT.2 v
  choose d hd using exists_rtr_dia Tr hK hL v
  have hsum : ∀ P ∈ Cu X u hK, (D.mem u).A.Nm v (dictA X Tr P) = dictA X Tr (∑ a, rtr X (d a) P) := by
    intro P hP
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Formalism.BasicNotions.ColumnsAtT.Nm, LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun a _ => (hd a P hP).2.symm
  have hmem : ∑ a, rtr X (d a) T.1 ∈ Cu X u hK := Submodule.sum_mem _ fun a _ => (hd a T.1 T.2).1
  have hz : (⟨_, hmem⟩ : Cu X u hK) = 0 :=
    hB.1 (((hsum T.1 T.2).symm.trans h0).trans (map_zero (colDictL X Tr hK)).symm)
  have hz' : ∑ a, rtr X (d a) T.1 = 0 := congrArg Subtype.val hz
  have e : ∑ a, rtr X (d a) S.1 = rtr X δ (∑ a, rtr X (d a) T.1) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, hS]
    exact Finset.sum_congr rfl fun a _ => rtr_comm (hδ (d a)) T.1
  show (D.mem u).A.Nm v (dictA X Tr S.1) = 0
  rw [hsum S.1 S.2, e, hz', map_zero, map_zero]

theorem sum_inner_rieszVector_rightTranslate (hK : X.LevelSubgroupCharacter) {ι : Type} [Fintype ι] (s : ι → Hfin X u)
    (hs : ∀ h, ∃! i, ∃ (γ : Gam X u) (κ : Ku X u hK), h = iotaF X u γ * s i * (κ : Hfin X u))
    (δ : Hfin X u) (hδ : ∀ k : Hfin X u, δ * k = k * δ) (T T' : Cu X u hK) :
    ∑ i, ⟪shP X u (rtr X δ T'.1) (s i), shP X u (rtr X δ T.1) (s i)⟫_ℂ =
      ∑ i, ⟪shP X u T'.1 (s i), shP X u T.1 (s i)⟫_ℂ := by
  simp only [Formalism.L2.SG.Pf.ColDictPf.rieszVector_rightTranslate]
  refine Formalism.L2.SG.Pf.ColDictPf.sum_reps X u (fun i => s i * δ) s (Ku X u hK) (fun h => ?_) hs
    (fun h => ⟪shP X u T'.1 h, shP X u T.1 h⟫_ℂ)
    (fun γ h κ => Formalism.L2.SG.Pf.ColDictPf.inner_shP_rat X u hK T T' γ h κ)
  have e : ∀ (i : ι) (γ : Gam X u) (κ : Ku X u hK), h * δ⁻¹ = iotaF X u γ * s i * (κ : Hfin X u) ↔
      h = iotaF X u γ * (s i * δ) * (κ : Hfin X u) := by
    intro i γ κ
    rw [mul_inv_eq_iff_eq_mul, mul_assoc _ (κ : Hfin X u) δ, ← hδ κ]
    simp only [mul_assoc]
  simpa only [e] using hs (h * δ⁻¹)

open Formalism.MainNotions _root_.Formalism.L2 Formalism.L2.DIV

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {R : Formalism.L2.RecT ex}


end GlobalTheory.MiTop.CenIsom

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchrodingerFunctionUnitaryLeviRadicalActions
section
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW

noncomputable section

namespace GlobalTheory.Core.Rk.SchLaws

variable {D : D7}

theorem isWeilDatumO_zero_one {ψ : AddChar (AF D.host.F) ℂ} {A B : HSp D} {χB : (AE D)ˣ →* Circle}
    {omh : WRep (dblSp A) B} (hW : IsWeilDatumO ψ (dblSp A) B 1 χB omh) :
    IsWeilDatumO ψ (zeroSp D) B 1 χB 1 := by
  refine
    { std := hW.std
      hecS := hW.hecS
      hecT := hW.hecT
      resS := ?_
      resT := hW.resT
      om_pres := fun _ _ hf => hf
      om_heis := ?_
      om_aut := fun _ _ _ _ _ _ => rfl
      om_cont := fun _ _ _ => continuous_const
      om_unit := fun _ _ _ _ _ _ _ => rfl
      om_split := ?_ }
  · refine ⟨hW.resS.1, fun η _ a => ?_⟩
    rw [show (zeroSp D).rank = 0 from rfl, pow_zero]
    rfl
  · intro g h w₀ f _
    have e : actO (zeroSp D) B g h w₀ = w₀ := Matrix.ext fun _ j => Fin.elim0 j
    rw [e]
    rfl
  · intro e _ g h _ _ x y hx _
    have hx1 : x = 1 := by
      apply Units.ext
      unfold IsDetAt at hx
      have : IsEmpty (Fin (zeroSp D).rank) := Fin.isEmpty
      rw [Matrix.det_isEmpty] at hx
      rw [hx]
      simp
    refine ⟨1, one_pos, fun ℓ _ f _ => ?_⟩
    simp [splitFacO, hx1]

theorem chr_gramOf_eq (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (x : Mx D B.rank A.rank) (c : skewA D A.rank) :
    chr ψ (gramOf B x) c = ψ ((dblDec A).qS B c x) := by
  rw [chr, HypDec.qS, HypDec.symplOH_extX_extY, pairS, adj_mul, mem_skewA.1 c.2, Matrix.mul_assoc, Matrix.neg_mul,
    Matrix.trace_neg, map_neg (trHalf D), Matrix.trace_mul_comm, gramOf]

theorem sch_laws : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) B), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ f, IsThetaFunO ψ (dblSp A) B f → (∀ h x, sch ψ A B ν 𝓨 (omh (1, h) f) x = sch ψ A B ν 𝓨 f (mt B h⁻¹ ⬝ x)) ∧ (∀ (m : GL (Fin A.rank) (AE D)) x, sch ψ A B ν 𝓨 (omh ((dblDec A).levi m, 1) f) x = ((χB⁻¹ (Matrix.GeneralLinearGroup.det m) : Circle) : ℂ) * npow (absA D (Matrix.GeneralLinearGroup.det m)) ((B.rank : ℂ) / 2) * sch ψ A B ν 𝓨 f (x ⬝ m.1)) ∧ (∀ c x, sch ψ A B ν 𝓨 (omh ((dblDec A).nC c, 1) f) x = chr ψ (gramOf B x) c * sch ψ A B ν 𝓨 f x) ∧ swSec A B omh ν 𝓨 f 1 = sch ψ A B ν 𝓨 f 0 := by
  intro D ψ A B χB omh hW ν 𝓨 hν f hf
  have h := GlobalTheory.MixSourceFormulas.mixed_source D ψ (dblSp A) (zeroSp D) B A.rank (dblDec A) 1 χB omh 1 hW
    (isWeilDatumO_zero_one hW) ν 𝓨 hν f hf
  refine ⟨fun g x => ?_, fun m x => ?_, fun c x => ?_, ?_⟩
  · exact congrFun (h.target g x) 0
  · calc
      _ = (((χB (Matrix.GeneralLinearGroup.det m))⁻¹ : Circle) : ℂ) *
          (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod B.rank m : ℂ) *
          sch ψ A B ν 𝓨 f (x ⬝ m.1) := congrFun (h.levi m x) 0
      _ = _ := by
        rw [MonoidHom.inv_apply, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod,
          GlobalTheory.Doubling.npow, Complex.ofReal_cpow (NNReal.coe_nonneg _)]
        push_cast
        rfl
  · rw [chr_gramOf_eq ψ A B]
    exact congrFun (h.centre c x) 0
  · rw [sch, mixS_dblDec_zero, GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.swSec, Prod.mk_one_one, map_one,
      one_apply_eq_self]

end GlobalTheory.Core.Rk.SchLaws

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawKernelLiftCombinationOfDefiniteClassData
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw

theorem kerX_of_clsPinD : ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), c.Is → (∀ s, (t s).Is) → ClsPinD t → KerX t := by
  intro D c 𝒯 t hc ht hP
  obtain ⟨ρ, hρ, hA⟩ := hP
  intro j hj y P
  have hj1 : j + 1 ≤ D.R.m := hj
  obtain ⟨hpos, hab⟩ := hρ.rk j hj
  obtain ⟨hB, ν, hν1, hνL, hmain⟩ := _root_.GlobalTheory.SeeSaw.lift_eq_classSum D c ρ hc hρ j hj1 hab
  obtain ⟨m', y', s, hinv, havg⟩ := @GlobalTheory.KJAvg.avg_span D.what₂.Tau _ (ρ.N j) (ρ.N (j + 1)) hab hpos (ρ.lam j) (ρ.n j)
    (GinfC (c.X j)) _ _ _ _ hB ν hν1 hνL (fun k τ => ρ.r j (Nat.le_of_succ_le hj1) k.1 τ) (hρ.uni j _) (ρ.fr j y).1
    (castP (ρ.hN j (Nat.le_of_succ_le hj1)) (ρ.hN (j + 1) hj1) P)
  have hz : ∀ i, ∀ τ, IsUnit ((fun τ => ρ.sc j τ • y' i τ) τ).det := by
    intro i τ
    simp only [Matrix.det_smul]
    exact (IsUnit.pow _ (Ne.isUnit (hρ.sc j τ))).mul (hinv i τ)
  let z : Fin m' → FrN D (ρ.N (j + 1)) := fun i => ⟨fun τ => ρ.sc j τ • y' i τ, hz i⟩
  let y'' : Fin m' → c.Fr (j + 1) := fun i => (ρ.fr (j + 1)).symm (z i)
  let cst : ℂ := ∏ τ, ((ρ.fr j y).1 τ).det ^ (-ρ.sS j τ)
  have key := hmain 1 (fun _ => y) (fun _ => P) m' y' y'' (fun i => cst * s i)
    (by intro i τ; simp only [y'', Equiv.apply_symm_apply]; rfl)
    (by
      intro F hF Λ
      rw [Fin.sum_univ_one, havg F hF Λ, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring)
  refine ⟨∑ i, Finsupp.single (y'' i) (cst * s i * ∏ τ, ((ρ.fr (j + 1) (y'' i)).1 τ).det ^ ρ.sD j τ), ?_⟩
  intro s' ψ hψ γ
  obtain ⟨⟨A, hA'⟩, _⟩ := hA s'
  have h1 := key (t s') A (ht s') hA' ψ hψ γ
  rw [Fin.sum_univ_one] at h1
  rw [h1]
  congr 1
  change _ = Finsupp.sum _ (fun y' b => b • (t s').rd (j + 1) γ ((t s').K j ψ) y')
  rw [Finsupp.sum_finsetSum _ _ (fun y' b => b • (t s').rd (j + 1) γ ((t s').K j ψ) y')
    (fun _ => zero_smul ℂ _) (fun _ _ _ => add_smul _ _ _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finsupp.sum_single_index (h := fun y' b => b • (t s').rd (j + 1) γ ((t s').K j ψ) y') (zero_smul ℂ _)]

end GlobalTheory.SeeSaw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawTupleKernelBackOfClassKernelData
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw

theorem castP_surjective {D : D7} {p q a b : ℕ} (hp : p = a) (hq : q = b) (Q : FP D.what₂.Tau a b) :
    ∃ P : PolF D q p, castP hp hq P = Q := by
  subst hp; subst hq
  refine ⟨Q, ?_⟩
  show MvPolynomial.rename _ Q = Q
  have : (fun v : D.what₂.Tau × Fin q × Fin p => (v.1, Fin.cast rfl v.2.1, Fin.cast rfl v.2.2)) = id := by
    funext v; simp
  rw [this, MvPolynomial.rename_id_apply]

theorem kBack_of_classData : ∀ (D : D7) (c : Comm D) (t : Tup c) (ρ : RealD c) (A : ClsK ρ t), c.Is → t.Is → ρ.Is → A.Is →
    (∀ j, j < D.R.m → t.cK j ≠ 0) → t.KBack := by
  intro D c t ρ A hc ht hρ hA hK j hj
  refine ⟨hK j hj, fun w => ?_⟩
  have hj1 : j + 1 ≤ D.R.m := hj
  have hab : ρ.N j ≤ ρ.N (j + 1) := (hρ.rk j hj).2
  obtain ⟨hB, ν, hν, -, hL⟩ := _root_.GlobalTheory.SeeSaw.lift_eq_classSum D c ρ hc hρ j hj1 hab
  haveI := hB
  haveI := hν
  set z : D.what₂.Tau → Matrix (Fin (ρ.N (j + 1))) (Fin (ρ.N (j + 1))) ℂ :=
    fun τ => (ρ.sc j τ)⁻¹ • (ρ.fr (j + 1) w).1 τ with hz
  obtain ⟨m, ys, Ps, hinv, havg⟩ := GlobalTheory.KJInf.subY_eq_sum_averages D.what₂.Tau (ρ.N j) (ρ.N (j + 1)) hab (ρ.lam j)
    (ρ.n j) (GinfC (c.X j)) ν (fun k => ρ.r j (Nat.le_of_succ_le hj1) k.1) (hρ.uni j _) z
  set s0 : ℂ := (∏ τ, ((ρ.fr (j + 1) w).1 τ).det ^ ρ.sD j τ)⁻¹ with hs0
  let y : Fin m → c.Fr j := fun i => (ρ.fr j).symm ⟨ys i, hinv i⟩
  have hy : ∀ i, (ρ.fr j (y i)).1 = ys i := fun i => congrArg Subtype.val ((ρ.fr j).apply_symm_apply ⟨ys i, hinv i⟩)
  have hP : ∀ i, ∃ P : PolF D (c.X (j + 1)).rank (c.X j).rank,
      castP (ρ.hN j (Nat.le_of_succ_le hj1)) (ρ.hN (j + 1) hj1) P = (s0 * ∏ τ, (ys i τ).det ^ ρ.sS j τ) • Ps i :=
    fun i => castP_surjective _ _ _
  choose P hP using hP
  refine ⟨m, y, P, fun ψ hψ γ => ?_⟩
  have hsc : ∀ (i : Fin 1) τ, (ρ.fr (j + 1) ((fun _ => w) i)).1 τ = ρ.sc j τ • (fun _ => z) i τ := by
    intro i τ
    simp only [hz]
    rw [smul_smul, mul_inv_cancel₀ (hρ.sc j τ), one_smul]
  have hav : ∀ F ∈ Vn (ρ.lam j) (ρ.n j), ∀ Λ : FP D.what₂.Tau (ρ.N j) (ρ.N (j + 1)) →ₗ[ℂ] ℂ,
      ∑ i, (∏ τ, ((ρ.fr j (y i)).1 τ).det ^ (-ρ.sS j τ)) *
        ∫ k, Λ (mvZ (fun τ => (ρ.r j (Nat.le_of_succ_le hj1) k.1 τ)⁻¹) (fun _ => 1)
          (castP (ρ.hN j (Nat.le_of_succ_le hj1)) (ρ.hN (j + 1) hj1) (P i))) *
          evalAt (fun τ => ρ.r j (Nat.le_of_succ_le hj1) k.1 τ * (ρ.fr j (y i)).1 τ) F ∂ν =
      ∑ i : Fin 1, (fun _ => s0) i * Λ (subY hab ((fun _ => z) i) F) := by
    intro F hF Λ
    clear hL
    have h0 := havg F hF Λ
    rw [Fin.sum_univ_one, ← h0, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e : (∏ τ, (ys i τ).det ^ (-ρ.sS j τ)) * ∏ τ, (ys i τ).det ^ ρ.sS j τ = 1 := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun τ _ => ?_
      rw [_root_.zpow_neg, inv_mul_cancel₀ (zpow_ne_zero _ (hinv i τ).ne_zero)]
    beta_reduce
    simp only [hy, hP, map_smul, smul_eq_mul, mul_assoc, integral_const_mul]
    linear_combination (s0 * ∫ k, Λ (mvZ (fun τ => (ρ.r j (Nat.le_of_succ_le hj1) k.1 τ)⁻¹) (fun _ => 1) (Ps i)) *
          evalAt (fun τ => ρ.r j (Nat.le_of_succ_le hj1) k.1 τ * ys i τ) F ∂ν) * e
  have hmain := hL m y P 1 (fun _ => z) (fun _ => w) (fun _ => s0) hsc hav t A ht hA ψ hψ γ
  have hs1 : s0 * ∏ τ, ((ρ.fr (j + 1) w).1 τ).det ^ ρ.sD j τ = 1 := by
    rw [hs0]
    refine inv_mul_cancel₀ (Finset.prod_ne_zero_iff.mpr fun τ _ => zpow_ne_zero _ ((ρ.fr (j + 1) w).2 τ).ne_zero)
  rw [hmain, Fin.sum_univ_one]
  simp only [hs1, one_smul]

end GlobalTheory.SeeSaw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilSectionDegeneratePrincipalSeriesLaw
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section

open GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw
namespace GlobalTheory.Core.Rk.SWLaw
variable {D : D7}

theorem scalar_eq (A B : HSp D) (χB : (AE D)ˣ →* Circle) (a : GL (Fin A.rank) (AE D)) :
    (((χB (Matrix.GeneralLinearGroup.det a))⁻¹ : Circle) : ℂ) * ((GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod B.rank a : ℝ) : ℂ) =
      ((χB⁻¹ (Matrix.GeneralLinearGroup.det a) : Circle) : ℂ) *
        npow (absA D (Matrix.GeneralLinearGroup.det a)) (sZero A B + (A.rank : ℂ) / 2) := by
  rw [MonoidHom.inv_apply, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod, npow, sZero, Complex.ofReal_cpow (NNReal.coe_nonneg _)]
  congr 2
  push_cast
  ring

theorem siegel_decomp (A : HSp D) (p : siegel A) :
    ∃ (a : GL (Fin A.rank) (AE D)) (c : skewA D A.rank), (p : GA D (dblSp A)) = (dblDec A).levi a * (dblDec A).nC c :=
  GlobalTheory.T.doublingSiegel_eq_levi_mul_unipotent D A p

theorem aP_decomp (A : HSp D) (p : siegel A) (a : GL (Fin A.rank) (AE D)) (c : skewA D A.rank)
    (h : (p : GA D (dblSp A)) = (dblDec A).levi a * (dblDec A).nC c) : aP A p = Matrix.GeneralLinearGroup.det a :=
  _root_.GlobalTheory.Core.Rk.SWLaw.aP_levi_mul_nC D A p a c h

theorem zero_datum (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle)
    (omh : WRep (dblSp A) B) (hW : IsWeilDatumO ψ (dblSp A) B 1 χB omh) (hP : GlobalTheory.Published.WeilRepresentationUnitaryPair) :
    ∃ om₀ : GA D (zeroSp D) × GA D B →* Module.End ℂ (WO (zeroSp D) B → ℂ), IsWeilDatumO ψ (zeroSp D) B 1 χB om₀ := by
  refine hP D ψ (zeroSp D) B 1 χB hW.std hW.hecS hW.hecT ?_ hW.resT
  exact ⟨hW.resS.1, fun η _ a => by rw [show (zeroSp D).rank = 0 from rfl, pow_zero]; rfl⟩

theorem swSec_law : GlobalTheory.Published.WeilRepresentationUnitaryPair → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) B), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓕 → ∀ φ, IsThetaFunO ψ (dblSp A) B φ → ∀ (p : siegel A) (g : GA D (dblSp A)), swSec A B omh ν 𝓕 φ (p * g) = (χB⁻¹ (aP A p) : Circle) * npow (absA D (aP A p)) (sZero A B + (A.rank : ℂ) / 2) * swSec A B omh ν 𝓕 φ g := by
  intro hP D ψ A B χB omh hW ν 𝓕 hν φ hφ p g
  obtain ⟨om₀, h₀⟩ := zero_datum ψ A B χB omh hW hP
  obtain ⟨a, c, hp⟩ := siegel_decomp A p
  have haP := aP_decomp A p a c hp
  have hν' : IsCovolOne (ratMx D B.rank A.rank) ν 𝓕 := hν
  have hF := hW.om_pres (g, 1) φ hφ
  set F := omh (g, 1) φ with hFdef
  have hF' := hW.om_pres ((dblDec A).nC c, 1) F hF
  have hM := _root_.GlobalTheory.MixSourceFormulas.mixed_source D ψ (dblSp A) (zeroSp D) B A.rank (dblDec A) 1 χB omh om₀ hW h₀ ν 𝓕 hν'
  have h1 := (hM _ hF').levi a 0
  have h2 := (hM F hF).centre c 0
  change (dblDec A).mixS B ψ ν 𝓕 (omh ((dblDec A).levi a, 1) (omh ((dblDec A).nC c, 1) F)) 0 =
    ((((χB (Matrix.GeneralLinearGroup.det a))⁻¹ : Circle) : ℂ) * (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod B.rank a : ℂ)) •
      (dblDec A).mixS B ψ ν 𝓕 (omh ((dblDec A).nC c, 1) F) (0 * a.1) at h1
  change (dblDec A).mixS B ψ ν 𝓕 (omh ((dblDec A).nC c, 1) F) 0 =
    ψ (symplOH (dblSp A) B ((dblDec A).extX B 0) ((dblDec A).extY B (0 * c.1))) •
      (dblDec A).mixS B ψ ν 𝓕 F 0 at h2
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.swSec
  have e1 : omh (↑p * g, 1) φ = omh ((dblDec A).levi a, 1) (omh ((dblDec A).nC c, 1) F) := by
    rw [hp, hFdef, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
    simp [Prod.mk_mul_mk, mul_assoc]
  rw [e1, ← mixS_dblDec_zero A B ψ ν 𝓕 _ 0, ← mixS_dblDec_zero A B ψ ν 𝓕 F 0, congrFun h1 0, Matrix.zero_mul, Pi.smul_apply, congrFun h2 0, map_zero, symplOH_zero_left, AddChar.map_zero_eq_one, one_smul, haP, smul_eq_mul]
  rw [scalar_eq A B χB a]

end GlobalTheory.Core.Rk.SWLaw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceIdempotentVacuumHyperspecialDictionaryStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (hyp IsVacAt UnrPl)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_idempotent_vacuum_hyperspecial_dictionary : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) = v → (IsSplit (E := D.host.E) v ↔ Formalism.DivisionValues.conjPl w ≠ w) ∧ (∀ χ : (AE D)ˣ →* Circle, (∀ w' : HeightOneSpectrum (𝓞 D.host.E), w'.under (𝓞 D.host.F) = v → UnrAt χ w') → UnrPl w χ) ∧ (∀ (V : HSp D) (g : GA D V), g ∈ hyp V w ↔ ∃ k ∈ Kv V v, g = embV V v k) ∧ (∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f : WO S T → ℂ), VacFin ψ S T v f → IsVacAt ψ S T w f) ∧ (IsSplit (E := D.host.E) v → ∀ χ : (AE D)ˣ →* Circle, UnrAt χ w → ∃ (e : AE D) (ϖ : 𝓞 D.host.E) (x : (AE D)ˣ), Formalism.L2.NTheta.IsIdemAt e w ∧ ϖ ∈ w.asIdeal ∧ ϖ ∉ w.asIdeal ^ 2 ∧ (x : AE D) = e * incA D (ϖ : D.host.E) + (1 - e) ∧ ∀ χ' : (AE D)ˣ →* Circle, UnrAt χ' w → ((χ' x : Circle) : ℂ) = ((val (F := D.host.F) χ' w : ℂˣ) : ℂ)) := by
  first | exact @GlobalTheory.PlaceDict.dictionary | exact GlobalTheory.PlaceDict.dictionary | (intros; apply GlobalTheory.PlaceDict.dictionary <;> assumption)
end

