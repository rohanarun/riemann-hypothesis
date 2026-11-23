module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0495
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0064
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0058
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0041
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0044
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0113
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0085
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0065
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0074
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1952
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0061
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0057
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0107
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0059
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0032
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0030
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0081
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0100
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryCommutationIdentity
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0116
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1819
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1708
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1775
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1758
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1792
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0487
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0461
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SizeBoundStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0115

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CommonLine
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1600000
namespace GlobalTheory.LineIdeal
section Loc
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.FinPlLoc NumberField GlobalTheory.AdelicU
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7}
end Loc
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues _root_.Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
open Matrix GlobalTheory.GoodPos
section Word
variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D} {u : D.what₂.Word}
  {ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ}
end Word
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
theorem single_alt (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (hW : _root_.GlobalTheory.Fam.PackageHypotheses W) (r : Fin D.R.rS) (hr : r.1 = 0) {u : D.what₂.Word} (f : _root_.GlobalTheory.Fam.FamilyCharacter W u)
    (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (hP : _root_.GlobalTheory.MiTop.PlacedConditions f B) (a₀ a₁ : GA D (D.sp.X 0)) (x : GlobalTheory.FinPl.Pl D)
    (hg : ∀ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ x) (hx : (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∉ x.asIdeal) {α cc : (AE D)ˣ}
    (hα : ∀ (S : Formalism.BasicNotions.TH.HSp D) (L : GlobalTheory.FinPl.Lat S) y,
      y ∈ latA S L (· = x) ↔ ((α⁻¹ : (AE D)ˣ) : AE D) • y ∈ latV S L (· = x))
    (hψ : ∀ s ∈ idAt D (· = x), (∀ o ∈ intAt D (· = x), psiE W.Q.Rl.ψ (s * o) = 1) ↔
      ((cc⁻¹ : (AE D)ˣ) : AE D) * s ∈ intAt D (· = x)) :
    ∀ a ∈ idAt D (· = x), mt (D.sp.Y 0) (_root_.GlobalTheory.MiTop.translationElement f B a₀ a₁)⁻¹ *ᵥ (a •
      (((cc ^ (D.R.rS - 1) * (α * α * (α * (xiU D * cU α)⁻¹) ^ D.R.rS) : (AE D)ˣ) : AE D) *
        incA D (D.host.xi0 ^ (D.R.m / 2) * (W.S.X.B.g : D.host.E) ^ D.R.rS)) •
      ratV fun k => W.S.X.ιE (W.S.X.eR r (Fin.cast (rank_eq W.S.X W.Q.instEq) k))) ∈ latV (D.sp.Y 0) ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) (· = x) ↔
      a ∈ intAt D (· = x) := by
  intro a ha
  obtain ⟨k, i1, i2, i3, i4, ι, v, o, n, G, pl, hc, -, ht, sh, -, -, hb, hp⟩ := hP
  obtain ⟨μ, lam, n1, n2, n3⟩ := hb.norm
  have hξ : -D.host.xi0 ^ (D.R.m / 2) ≠ 0 := neg_ne_zero.2 (pow_ne_zero _ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D))
  have hμ : μ ≠ 0 := left_ne_zero_of_mul (n1 ▸ hξ)
  have hlam : lam ≠ 0 := right_ne_zero_of_mul (n1 ▸ hξ)
  have h₀ : 0 + 2 * D.R.rS + 2 = D.R.m := by
    obtain ⟨c, hc⟩ := D.R.m_even
    have := D.R.two_le_m
    unfold Ranks.rS
    omega
  obtain ⟨s, hs, he⟩ := first_vec (_root_.GlobalTheory.MiTop.formsAtZero W u) (W.S.tr u) hW.bot.idE hc.std B hμ n2 r hr
  have hI := all_ideal hc sh (fun n h x hx => by subst h; exact hp x hx) (fun j hj => by
      change 0 < (D.sp.X (j + 1)).rank
      rw [Formalism.L2.Forms.rankN D _ hj]
      unfold Ranks.N
      have := D.R.m_add_three_le_k
      omega) hlam n3 (fun e => hx ((ht.tP x).1 e)) hα hψ 0 D.R.rS h₀ (D.R.rS - 1) r (by have := r.2; omega)
  have hd : B.d.e = (f.c.bes 0 D.R.rS h₀).d.e := eq_of_heq (Sigma.mk.inj (congrArg
    (fun Z : BesLev D D.R.rS => (⟨Z.V.rank, Z.d.e⟩ : Σ n, Matrix (Fin n) (Fin D.R.rS) D.host.E)) (hb.lev h₀))).2
  have hm := ht.moves 0 (by omega) (· = x) fun p hp e => by
    obtain ⟨PP, h1, h2⟩ := (ht.gP p).1 e
    exact hg PP h1 (h2.symm.trans hp)
  have hx1 := xu_fixes (h := W.Q.instEq) (u := u) hW.bot.idE r
  rw [← mul_assoc (α * α), ← mul_assoc (cc ^ _)] at hI
  generalize cc ^ (D.R.rS - 1) * (α * α * (α * (xiU D * cU α)⁻¹) ^ D.R.rS) = K at hI ⊢
  obtain ⟨ε, hε⟩ : ∃ ε : Fin (D.sp.Y 0).rank → D.host.E,
      (fun k => W.S.X.ιE (W.S.X.eR r (Fin.cast (rank_eq W.S.X W.Q.instEq) k))) = ε := ⟨_, rfl⟩
  have he' : ∀ k, B.d.e k r = s * (μ * (W.S.X.B.g : D.host.E) ^ D.R.rS) * ε k := fun k => by rw [he, ← hε]
  rw [hε] at hx1 ⊢
  have hss : s * s = 1 := by rcases hs with rfl | rfl <;> simp
  have hy : a • ((K : AE D) * incA D (D.host.xi0 ^ (D.R.m / 2) * (W.S.X.B.g : D.host.E) ^ D.R.rS)) • ratV ε =
      colMul B.d.jX r ((K : AE D) * incA D lam * (incA D (-s) * a)) := by
    funext k
    change a * (_ * incA D (ε k)) = _ * incA D (B.d.e k r)
    have : D.host.xi0 ^ (D.R.m / 2) * (W.S.X.B.g : D.host.E) ^ D.R.rS * ε k = lam * -s * B.d.e k r := by
      rw [he']
      linear_combination ((W.S.X.B.g : D.host.E) ^ D.R.rS * ε k) * n1 + (lam * μ * (W.S.X.B.g : D.host.E) ^ D.R.rS * ε k) * hss
    have h2 := congrArg (incA D) this
    rw [map_mul, map_mul (incA D) (lam * -s), map_mul (incA D) lam] at h2
    linear_combination (a * K) * h2
  have hfix : mt (D.sp.Y 0) ((show GA D (D.sp.Y 0) from f.g.b 0) * (_root_.GlobalTheory.MiTop.translationElement f B a₀ a₁)⁻¹) *ᵥ
      (a • ((K : AE D) * incA D (D.host.xi0 ^ (D.R.m / 2) * (W.S.X.B.g : D.host.E) ^ D.R.rS)) • ratV ε) =
      colMul B.d.jX r ((K : AE D) * incA D lam * (incA D (-s) * a)) := by
    have e : (show GA D (D.sp.Y 0) from f.g.b 0) * (_root_.GlobalTheory.MiTop.translationElement f B a₀ a₁)⁻¹ =
        embA B.d B.o (a₀ * a₁)⁻¹ * (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) := by
      unfold _root_.GlobalTheory.MiTop.translationElement
      rw [map_inv, _root_.mul_inv_rev, mul_inv_cancel_left, _root_.mul_inv_rev, inv_inv]
    rw [e, GlobalTheory.MixModel.mt_mul, ← mulVec_mulVec, mulVec_smul (mt _ ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))), mulVec_smul (mt _ ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))), hx1, hy]
    generalize (K : AE D) * incA D lam * (incA D (-s) * a) = t
    have e1 : colMul B.d.jX r t = B.d.jX *ᵥ Pi.single r t := by
      rw [mulVec_single]; funext k; exact mul_comm _ _
    rw [e1, mulVec_mulVec, embA_apply, B.d.wittDecomp_anisotropicEmbedding_inclX]
  have hsup : ∀ i, (a • ((K : AE D) * incA D (D.host.xi0 ^ (D.R.m / 2) * (W.S.X.B.g : D.host.E) ^ D.R.rS)) • ratV ε) i ∈
      idAt D (· = x) := fun i => Ideal.mul_mem_right _ _ ha
  rw [GlobalTheory.MixModel.mt_mul, ← mulVec_mulVec] at hfix
  have hj : B.d.jX = (f.c.bes 0 D.R.rS h₀).d.jX := congrArg rat hd
  have h1 := hI ((K : AE D) * incA D lam * (incA D (-s) * a)) (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ ha))
  rw [← inU_val lam hlam, ← Units.val_mul, Units.inv_mul_cancel_left, Units.val_mul, inU_val, ← hj] at h1
  refine (hm _ (GlobalTheory.FinPl.KOpen.supp_mulVec (D.sp.Y 0) _ _ hsup)).trans
    ((iff_of_eq (congrArg (· ∈ latV (D.sp.Y 0) (v.N 0) (· = x)) hfix)).trans (h1.trans ?_))
  rcases hs with rfl | rfl
  · rw [map_neg, map_one, neg_one_mul, int_neg]
  · rw [neg_neg, map_one, one_mul]
theorem common_line_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → 1 ≤ D.R.rS → ∀ u u' (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (f' : _root_.GlobalTheory.Fam.FamilyCharacter W u') (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (B' : SBes W.S.X W.Q.instEq u' W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedConditions f B → _root_.GlobalTheory.MiTop.PlacedConditions f' B' → ∀ a₀ a a₀' a', _root_.GlobalTheory.MiTop.IsTranslate' f B a₀ a → _root_.GlobalTheory.MiTop.IsTranslate' f' B' a₀' a' → ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (∀ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ v) → (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal → (((D.mem u').A.T : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal → ∃ w : Fin (D.sp.Y 0).rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E, ∀ c : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E, ((∃ x ∈ GlobalTheory.AdelicU.latLoc D.host.F ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) v, Matrix.mulVec (GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) D.sp.cm.sig (D.sp.Y 0).gram (GlobalTheory.AdelicU.proj D.sp.cm.sig (D.sp.Y 0).gram v (_root_.GlobalTheory.MiTop.translationElement f B a₀ a))).1 x = c • w) ↔ c ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v) ∧ ((∃ x ∈ GlobalTheory.AdelicU.latLoc D.host.F ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) v, Matrix.mulVec (GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) D.sp.cm.sig (D.sp.Y 0).gram (GlobalTheory.AdelicU.proj D.sp.cm.sig (D.sp.Y 0).gram v (_root_.GlobalTheory.MiTop.translationElement f' B' a₀' a'))).1 x = c • w) ↔ c ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v) := by
  intro D L hT Gi Gl Kc Yd cX ex W hW hr u u' f f' B B' hP hP' a₀ a a₀' a' _ _ v hg hu hu'
  have hstd : IsStdChar D W.Q.Rl.ψ (-1) := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hc, -⟩ := hP
    exact hc.std
  obtain ⟨α, hα⟩ := GlobalTheory.IdeleAA.exists_idele_AA D _ hstd
  have hψ : ∀ s ∈ idAt D (· = v), (∀ o ∈ intAt D (· = v), psiE W.Q.Rl.ψ (s * o) = 1) ↔
      (((xiU D * α * cU α)⁻¹ : (AE D)ˣ) : AE D) * s ∈ intAt D (· = v) := fun s hs => by
    rw [(hα v).2 s hs, mul_inv, mul_inv, Units.val_mul, Units.val_mul, cU_inv, xiU, inU_inv]
  have hfg : ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0).FG := (_root_.GlobalTheory.Fam.sdY_frames_alt W hW 0 (by have := D.R.two_le_m; omega)).1.1.fg
  exact ⟨_, fun c => ⟨line_loc (D.sp.Y 0) _ hfg v _ _ (_root_.GlobalTheory.LineIdeal.single_alt W hW ⟨0, hr⟩ rfl f B hP a₀ a v hg hu (hα v).1 hψ) c,
    line_loc (D.sp.Y 0) _ hfg v _ _ (_root_.GlobalTheory.LineIdeal.single_alt W hW ⟨0, hr⟩ rfl f' B' hP' a₀' a' v hg hu' (hα v).1 hψ) c⟩⟩
end GlobalTheory.LineIdeal
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EigSlopeLe
section
set_option synthInstance.maxHeartbeats 200000

section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.DefEig
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}
theorem actKeeps_alt (p : PtAt ex Csz) (i : Fin D.R.m) (hp : p.PointConditions') : ActKeeps (κ := p.κ) p.O i := fun g f hf => by
  obtain ⟨cc, ph, hO⟩ := (hp.oneMap i).1
  obtain ⟨k, hk, -⟩ := (p.pins i).2.lift.lev g
  exact (hO.1 g k hk f hf).1
theorem exists_chi_algebraMap_eq_FW_chi_mul_psi_inv (p : PtAt ex Csz) (i : Fin D.R.m) (hp : _root_.GlobalTheory.CovTop.RowsTAlt p) :
    ∃ χ : (p.F.lv2.lvl false).P →* (p.T.Q.c.F)ˣ, ∀ u, algebraMap p.T.Q.c.F D.what₂.LL (χ u : p.T.Q.c.F) =
      (((p.R.toRealDat.FW i).chi u * (p.F.lv2.lvl false).ψ⁻¹ u : D.what₂.LLˣ) : D.what₂.LL) := by
  have hv := _root_.GlobalTheory.CovTop.chi_mul_psi_inv_mem_core_alt p i hp.1 hp.2
  choose b hb using hv
  have hinj : Function.Injective (algebraMap p.T.Q.c.F D.what₂.LL) := (algebraMap p.T.Q.c.F D.what₂.LL).injective
  have hb0 : ∀ u, b u ≠ 0 := fun u h => by
    have := hb u
    rw [h, map_zero] at this
    exact Units.ne_zero _ this.symm
  refine ⟨{ toFun := fun u => Units.mk0 (b u) (hb0 u), map_one' := ?_, map_mul' := ?_ }, fun u => hb u⟩
  · refine Units.ext (hinj ?_)
    simp [hb]
  · intro u v
    refine Units.ext (hinj ?_)
    simp only [Units.val_mk0, Units.val_mul, map_mul, hb, Subgroup.coe_mul, MonoidHom.inv_apply]
    push_cast
    ring
set_option maxHeartbeats 1000000 in
theorem exists_finite_group_lev_char_slope : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (PP A M : ℝ), _root_.GlobalTheory.CovTop.RowsTAlt p → (i : ℕ) + 1 = D.R.m → GramAt p i → WtNum p i PP → HostNum D L PP A M → FnAlgClosed (Xo := (p.T.Q.Xo ((i : ℕ) + 1))) (c := p.T.Q.c) → ∃ (G : Type) (_ : Group G) (_ : Finite G) (lev : G → ((dat p i).La →ₗ[𝓞 D.host.E] (dat p i).La) × ((dat p i).La →ₗ[𝓞 D.host.E] (dat p i).La)) (χ : G →* (p.T.Q.c.F)ˣ), ActLev (Xo := p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c lev ∧ FreePt (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c lev ∧ slope_sq (normW (p.T.U ((i : ℕ) + 1)) (xiR D) (p.T.V ((i : ℕ) + 1)) (p.T.dict ((i : ℕ) + 1)) (Gk p i)) (eigLat (p.T.U ((i : ℕ) + 1)) lev χ (Gk p i)) ≤ muCore p i := by
  intro D L hT Gi Gl Kc Y0 cX ex Csz p i PP A M hp hi hG hW hH hF
  obtain ⟨χ, hχ⟩ := _root_.GlobalTheory.DefEig.exists_chi_algebraMap_eq_FW_chi_mul_psi_inv p i hp
  have hK := _root_.GlobalTheory.DefEig.actKeeps_alt p i hp.1
  have hρ := (p.rhoGeo i).1 hK
  have hsm : ∀ (u : (p.F.lv2.lvl false).P) (f : p.T.cuspA ((i : ℕ) + 1) (wtA (p.κ i)) (p.κ i).n),
      ((p.fw.e i (((χ u : (p.T.Q.c.F)ˣ) : p.T.Q.c.F) • f) : (p.R.FW i).WK) : Fin (p.R.nW i) → D.what₂.LL) =
        (((p.R.toRealDat.FW i).chi u * (p.F.lv2.lvl false).ψ⁻¹ u : D.what₂.LLˣ) : D.what₂.LL) •
          ((p.fw.e i f : (p.R.FW i).WK) : Fin (p.R.nW i) → D.what₂.LL) := fun u f => by
    rw [LinearEquiv.map_smul, Submodule.coe_smul, ← hχ u, algebraMap_smul]
  refine ⟨(p.F.lv2.lvl false).P, inferInstance, inferInstance, fun g => (p.O i).lev2 (g : p.P.Gp), χ, actLev_levB p i,
    _root_.GlobalTheory.T.freePt_last_index_of_fnAlgClosed p i PP A M hp hi hG hW hH hF, le_of_eq ?_⟩
  have hAB : ((eigSub (Xo := p.T.Q.Xo ((i : ℕ) + 1)) (c := p.T.Q.c)
        (fun g : (p.F.lv2.lvl false).P => (p.O i).lev2 (g : p.P.Gp)) χ).comap
        (cuspW (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c (p.T.U ((i : ℕ) + 1)) (Gk p i)).subtype).restrictScalars (𝓞 p.T.Q.c.F) =
      ((Submodule.span p.T.Q.c.F (typeK p.fw p.F.lv2 i)).comap (VK p.fw i).subtype).restrictScalars (𝓞 p.T.Q.c.F) := by
    ext x
    change (x : p.T.R ((i : ℕ) + 1)) ∈ eigSub (Xo := p.T.Q.Xo ((i : ℕ) + 1)) (c := p.T.Q.c)
        (fun g : (p.F.lv2.lvl false).P => (p.O i).lev2 (g : p.P.Gp)) χ ↔
      (x : p.T.R ((i : ℕ) + 1)) ∈ Submodule.span p.T.Q.c.F (typeK p.fw p.F.lv2 i)
    have hx : (x : p.T.R ((i : ℕ) + 1)) ∈ p.T.cuspA ((i : ℕ) + 1) (wtA (p.κ i)) (p.κ i).n := by
      exact (cuspW_wtZ (Xo := p.T.Q.Xo ((i : ℕ) + 1)) (c := p.T.Q.c) (U := p.T.U ((i : ℕ) + 1))
        (wtA (p.κ i)) (p.κ i).n).le x.2
    constructor
    · intro h
      rw [mem_eigSub_iff] at h
      apply Submodule.subset_span
      refine ⟨hx, fun u => ?_⟩
      obtain ⟨hf', h2⟩ := hρ (u : p.P.Gp) ⟨x, hx⟩
      rw [← h2]
      have h3 : (⟨actLev p.T.Q.c (p.O i).lev2 (u : p.P.Gp) (x : p.T.R ((i : ℕ) + 1)), hf'⟩ :
          p.T.cuspA ((i : ℕ) + 1) (wtA (p.κ i)) (p.κ i).n) = ((χ u : (p.T.Q.c.F)ˣ) : p.T.Q.c.F) • ⟨x, hx⟩ :=
        Subtype.ext (h u)
      exact (congrArg (fun y => ((p.fw.e i y : (p.R.FW i).WK) : Fin (p.R.nW i) → D.what₂.LL)) h3).trans (hsm u ⟨x, hx⟩)
    · intro h
      refine Submodule.span_le.2 ?_ h
      rintro f ⟨hf, hT⟩
      rw [SetLike.mem_coe, mem_eigSub_iff]
      intro u
      obtain ⟨hf', h2⟩ := hρ (u : p.P.Gp) ⟨f, hf⟩
      have h4 : (p.R.FW i).ρ (u : p.P.Gp) ((p.fw.e i ⟨f, hf⟩ : (p.R.FW i).WK) : Fin (p.R.nW i) → D.what₂.LL) =
          (((p.R.toRealDat.FW i).chi u * (p.F.lv2.lvl false).ψ⁻¹ u : D.what₂.LLˣ) : D.what₂.LL) •
            ((p.fw.e i ⟨f, hf⟩ : (p.R.FW i).WK) : Fin (p.R.nW i) → D.what₂.LL) := hT u
      have h5 : (p.fw.e i ⟨actLev p.T.Q.c (p.O i).lev2 (u : p.P.Gp) f, hf'⟩) =
          p.fw.e i (((χ u : (p.T.Q.c.F)ˣ) : p.T.Q.c.F) • ⟨f, hf⟩) := by
        exact Subtype.ext (h2.trans (h4.trans (hsm u ⟨f, hf⟩).symm))
      exact congrArg Subtype.val ((p.fw.e i).injective h5)
  have key : eigLat (p.T.U ((i : ℕ) + 1)) (fun g : (p.F.lv2.lvl false).P => (p.O i).lev2 (g : p.P.Gp)) χ (Gk p i) =
      latTypeK p.fw p.F.lv2 i :=
    congrArg (latW (p.T.U ((i : ℕ) + 1)) (Gk p i) ⊓ ·) hAB
  rw [muCore, ← key]
end GlobalTheory.DefEig
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsReadsLowStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_quadratic_extension_reads_low_of_true : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → (commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).Is → ∀ t, ∃ J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t, J.ReadsLow := by
  first | exact @_root_.GlobalTheory.LowJoin.exists_quadratic_extension_readsLow | exact _root_.GlobalTheory.LowJoin.exists_quadratic_extension_readsLow | (intros; apply _root_.GlobalTheory.LowJoin.exists_quadratic_extension_readsLow <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsReadsStd
section
set_option synthInstance.maxHeartbeats 200000

section
set_option genSizeOfSpec false
set_option genInjectivity false
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.PenChart
section Orbits
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]
end Orbits
section Restr
variable {D : D7} {c : Comm D} {v : VCom c} {Bs : GlobalTheory.Fam.Base c} {PP : Pl D.host.E} {G : QGeo v Bs PP} {χ : ℕ → (AE D)ˣ →* Circle}
end Restr
section Place
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}
  {Ch₀ : ℕ → Type} (A : TwDat I l Z u a Ch₀)
  {c : Comm (I.rec7 l Z)} {v : VCom c} {Bs : GlobalTheory.Fam.Base c} {PP : Pl (I.rec7 l Z).host.E} {G : QGeo v Bs PP}
  {χ : ℕ → (AE (I.rec7 l Z))ˣ →* Circle} (E : QExt G χ)
variable {A E} {P : BadPr I a} {hψ : Continuous G.ψk} {sg : ℂ}
end Place
section Level
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}
  {Ch₀ : ℕ → Type} {A : TwDat I l Z u a Ch₀} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end Level
set_option maxHeartbeats 4000000 in
theorem exists_readsStd_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → (commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).Is → ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.ReadsLow → ∃ J' : _root_.GlobalTheory.Fam.QuadraticExtensionData a t, J'.ReadsStd := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha ha' hc t J h
  have hI := hW.tr.ok
  have ht := hW.tr.tw
  have h2 := B.R.two_le_m
  have hs : ∀ i, (J.G i).s + 1 + 1 = B.R.m := fun i => (J.G i).hs
  have hPi : Function.Injective J.P := fun i i' e => h.inj ((h.eq i).symm.trans ((congrArg Subtype.val e).trans (h.eq i')))
  have hPs : ∀ P : BadPr I (W.P.I.tup t), P.1 ∈ I.Q (W.P.I.tup t) → ∃ i, J.P i = P := fun P hP => by
    obtain ⟨i, e⟩ := h.surj P.1 ((hW.tq.Q t P.1).2 hP)
    exact ⟨i, Subtype.ext ((h.eq i).trans e)⟩
  have hQ : ∀ i, (J.P i).1 ∈ I.Q (W.P.I.tup t) := fun i => (Finset.mem_union.1 (J.P i).2).resolve_left (h.tw i).nmem
  have hbox : ∀ i j, j + 1 ≠ B.R.m → ∀ y, InBox (J.E i) j y := fun i j hj y e => hj ((congrArg (· + 1) e).trans (hs i)) |>.elim
  have kπ : ∀ i j (β : J.Ch₀ j), ∃ y : {y : (J.E i).Ch j // InBox (J.E i) j y},
      (j + 1 ≠ B.R.m → y.1 = J.π i j β) ∧ OrbAt J.A (J.E i) j y.1 β := fun i j β => by
    by_cases hj : j + 1 = B.R.m
    · obtain ⟨y, h1, h3⟩ := exists_orbAt hI h.is (h.tw i) (h.M i) hj β (h.std j (by omega) β)
      exact ⟨⟨y, h1⟩, fun e => absurd hj e, h3⟩
    · exact ⟨⟨J.π i j β, hbox i j hj _⟩, fun _ => rfl, fun e => (hj ((congrArg (· + 1) e).trans (hs i))).elim⟩
  choose π hπ hπ' using kπ
  have kι : ∀ j (y : ∀ i, {y : (J.E i).Ch j // InBox (J.E i) j y}), ∃ β : J.Ch₀ j,
      (j + 1 ≠ B.R.m → β = J.ι j fun i => (y i).1) ∧
      (j + 1 = B.R.m → Good (J.A.p0 j β) ∧ ∀ i, OrbAt J.A (J.E i) j (y i).1 β) := fun j y => by
    by_cases hj : j + 1 = B.R.m
    · let b := J.A.b0 j (J.ι j fun i => (y i).1)
      choose z hz hz' using fun i => exists_vec hI h.is (h.tw i) (h.M i) hj b (y i).2
      obtain ⟨β, hβ, hβ'⟩ := exists_chart hI ht h.is hj b (Function.extend J.P z 0) fun P hP => by
        obtain ⟨i, rfl⟩ := hPs P ((Finset.mem_union.1 P.2).resolve_left hP)
        rw [hPi.extend_apply]
        exact hz i
      refine ⟨β, fun e => absurd hj e, fun _ => ⟨hβ, fun i => hz' i (hQ i) β (h.std j (by omega) β) ?_⟩⟩
      have := hβ' (J.P i) (hQ i)
      rwa [hPi.extend_apply] at this
    · exact ⟨_, fun _ => rfl, fun e => absurd e hj⟩
  choose ι hι hι' using kι
  have hsec : ∀ j, j ≤ B.R.m → ∀ y i, π i j (ι j y) = y i := fun j hj y i => by
    refine Subtype.ext ?_
    by_cases e : j + 1 = B.R.m
    · exact orbAt_unique e (hπ' i j _) ((hι' j y e).2 i)
    · rw [hπ i j _ e, hι j y e]
      exact h.sec j hj e _ i
  have hlift : ∀ j, j + 1 ≠ B.R.m → ∀ y, J.ι j y ∈ Set.range (ι j) := fun j hj y =>
    ⟨fun i => ⟨y i, hbox i j hj _⟩, hι j _ hj⟩
  let J' : _root_.GlobalTheory.Fam.QuadraticExtensionData a t := ⟨J.Ch₀, J.A, J.r, J.pl, J.mem, fun i => restr (J.E i), J.P, J.hψ, J.sg, π, ι⟩
  refine ⟨J', h.is, h.inj, h.surj, h.chr, h.res, h.eq, h.sg, h.tw, h.M, fun i j d e hj β => ?_, fun i β => hπ' i _ β rfl, h.std, h.last,
    hsec, fun n y e he r => ?_, fun j => ?_, fun β => ?_, fun β => ?_, fun j hj γ hγ α z => ?_⟩
  · have e' : j + d = (J.G i).s := e
    have := h.rep i j d e hj β
    rw [← hπ i j β (by have := hs i; omega)] at this
    exact this
  · have hn : (a.G n).s + 1 + 1 = B.R.m := (a.G n).hs
    have hP : (a.pl n).1 ∈ (B.primes X).vGs := (hW.lev.2.1 _).1 (a.pl n).2
    obtain ⟨h3, h4⟩ := _root_.GlobalTheory.T.true_geometry_commutation_twist_alt W hW u a ha ha' hc n
    exact couplingCoset_sub_basePoint_integral_typePrime hI h.is hn (a.G n).S ((a.G n).q.pr.comp (incA (I.rec7 l Z))) ⟨(a.pl n).1, Finset.mem_union_left _ hP⟩ hP h3 h4 _
      (h.std _ (by omega) _) (hι' _ y hn).1 e he r
  · by_cases e : j + 1 = B.R.m
    · exact fun y y' hy => funext fun i => (hsec j (by omega) y i).symm.trans
        ((congrArg (π i j) hy).trans (hsec j (by omega) y' i))
    · intro y y' hy
      have h3 := h.injCh j e ((hι j y e).symm.trans (hy.trans (hι j y' e)))
      exact funext fun i => Subtype.ext (congrFun h3 i)
  · obtain ⟨y, rfl⟩ := h.first β
    exact hlift 0 (by omega) y
  · obtain ⟨y, rfl⟩ := h.onto β
    exact hlift _ (by omega) y
  · by_cases e : j + 1 + 1 = B.R.m
    · by_contra hz
      refine hγ ⟨fun i => π i (j + 1) γ, ?_⟩
      refine chart_ext hI ht h.is e (J.A.b0 _ γ) _ _ (hι' _ _ e).1 (good_of_xi hI ht e hj α γ z hz) fun P hP => ?_
      obtain ⟨i, rfl⟩ := hPs P hP
      exact lev_of_orbAt hI h.is (h.tw i) (h.M i) e _ hP (h.std _ (by omega) _) (h.std _ (by omega) _) ((hι' _ _ e).2 i) (hπ' i _ γ)
    · refine h.dead j hj e γ ?_ α z
      rintro ⟨y, rfl⟩
      exact hγ (hlift _ e y)
end GlobalTheory.PenChart
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsRunsAtStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.runs_estimate_statement' : _root_.GlobalTheory.BigOn.TwoRunsStatement := by
  first | exact @_root_.GlobalTheory.BigOn.bigOn_runsSt | exact _root_.GlobalTheory.BigOn.bigOn_runsSt | (intros; apply _root_.GlobalTheory.BigOn.bigOn_runsSt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExtremalVectorsSplitPartStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_estimate_statement' : _root_.GlobalTheory.BigOn.RationalityStatement' := by
  first | exact @_root_.GlobalTheory.BigOn.bigOn_ratSt | exact _root_.GlobalTheory.BigOn.bigOn_ratSt | (intros; apply _root_.GlobalTheory.BigOn.bigOn_ratSt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamOfEpsMemStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] _root_.GlobalTheory.Fam.GeometricFamily.fld _root_.GlobalTheory.Fam.GeometricFamily.val _root_.GlobalTheory.Fam.GeometricFamily.top _root_.GlobalTheory.Fam.GeometricFamily.loc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_joint_twist_data_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ (J : ∀ t, _root_.GlobalTheory.Fam.QuadraticExtensionData a t), (∀ t, (J t).Reads) → ∀ (row : ∀ t, RowCh (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u a.g t)
    (col : ∀ t : W.P.T, ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u (W.P.I.tup t))) (hCh : ∀ t, (col t).Ch = (J t).Ch) (sc cT : ℕ → ℂ) t, ∀ j α, ∀ g ∈ (((_root_.GlobalTheory.Fam.familyOfRowColumnChoices a J row col hCh t).pinTup sc cT).ε j α).support,
    g ∈ GlobalTheory.FinPl.grpAt (Yc (I.rec7 l Z) j) (· ∈ ((_root_.GlobalTheory.Fam.familyOfRowColumnChoices a J row col hCh t).pinTup sc cT).Q) ∧ g * a.g.b j ∈ GfC (Yc (I.rec7 l Z) j) := by
  first | exact @_root_.GlobalTheory.Fam.famOf_eps_mem_alt | exact _root_.GlobalTheory.Fam.famOf_eps_mem_alt | (intros; apply _root_.GlobalTheory.Fam.famOf_eps_mem_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SizeAltBisStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cov_size_bound : _root_.GlobalTheory.CovTop.SizeCondition := by
  first | exact @_root_.GlobalTheory.CovTop.SizeRows.size_alt_bis | exact _root_.GlobalTheory.CovTop.SizeRows.size_alt_bis | (intros; apply _root_.GlobalTheory.CovTop.SizeRows.size_alt_bis <;> assumption)
end
end

