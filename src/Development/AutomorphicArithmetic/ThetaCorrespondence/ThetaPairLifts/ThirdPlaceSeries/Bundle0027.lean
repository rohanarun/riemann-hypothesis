module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0216
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0020
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0019
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0367
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CGTrueT
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle0008

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsTerTer
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.BlockType GlobalTheory.SplitWeil
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.TypeBlockConj
end GlobalTheory.TypeBlockConj
namespace GlobalTheory.TypeBlockConj
set_option maxHeartbeats 1000000 in
theorem main_alt_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (S : Reading P.T), _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (s : SplitPlace D.host.E) (hw : IsSplitPl D.host s.w), s.w = GlobalTheory.DimPartsCompare.cPl (D.naut.plGw k v) → IsTame (S i s.w hw).mu → ∀ c : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E, Continuous c → (∀ x : D.host.E, c (s.i x) = algebraMap D.host.E (s.w.adicCompletion D.host.E) x) → ∀ Q, ∃ f ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q), f ≠ 0 ∧ ∀ x : GAf D.host.E D.R.nV, TrivOutside {s.v} x → Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x) ∈ blockGrp (s.w.adicCompletion D.host.E) D.R.r D.R.t → NG.rt D.host.E D.R.nV x f = blockChar (S i s.w hw).mu (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) • f := by
  intro hL D P S hS i k v s hw hs hμt c hc hcs Q
  obtain ⟨hj1, hj2⟩ := D.nd.j_range i
  let j : Fin D.R.m := ⟨D.nd.j i - 1, by omega⟩
  have hj : j.1 + 1 = D.nd.j i := by simp only [j]; omega
  have hconj : IsConjPl D.host (D.naut.plGw k v) s.w := by
    rw [hs]; exact GlobalTheory.DimPartsCompare.isConjPl_cPl _
  obtain ⟨hw₀, hi₀⟩ := _root_.GlobalTheory.TypeTame.conjSP_w_of_isConjPl D s _ hconj
  obtain ⟨ψ₀, ξ, hψ, hξ, hU⟩ := P.H.level.uni i j hj k v (GlobalTheory.TypeTame.conjSP s) hw₀
  have hcc : ∀ x : D.host.E, D.host.conj (D.host.conj x) = x := fun x => by
    letI := Formalism.BasicNotions.Host.cmStar D.host
    rw [← GlobalTheory.DimPartsCompare.star_conj, ← GlobalTheory.DimPartsCompare.star_conj, star_star]
  have hcsd : IsCSD D.host (P.tp.tup (D.nd.mu i) j) := by
    have := (P.chr.csd _).1 (D.naut.muC_csd i)
    rwa [P.chr.muC i j hj] at this
  have hconj' : IsConjPl D.host s.w (D.naut.plGw k v) := by
    have := GlobalTheory.DimPartsCompare.isConjPl_cPl (GlobalTheory.DimPartsCompare.cPl (D.naut.plGw k v))
    rwa [GlobalTheory.DimPartsCompare.cPl_cPl, ← hs] at this
  have hμ := hS.mu i s.w hw j hj
  have hrel : ∀ u, ξ⁻¹ u = (S i s.w hw).mu (Units.map c.toMonoidHom u) := by
    refine _root_.GlobalTheory.ConjDense.eq_of_agree s c hc hcs _ _ hμ.1 ?_ ?_
    · obtain ⟨N, hN⟩ := hξ.1
      exact ⟨N, fun u hu => by rw [MonoidHom.inv_apply, hN u hu, inv_one]⟩
    · intro x
      have e1 : Units.map (s.i : D.host.E →* s.v.adicCompletion (maximalRealSubfield D.host.E)) x =
          Units.map ((GlobalTheory.TypeTame.conjSP s).i : D.host.E →* s.v.adicCompletion (maximalRealSubfield D.host.E))
            (Units.map (MonoidHomClass.toMonoidHom D.host.conj) x) := by
        ext
        simp [hi₀]
        change _ = (s.i (D.host.conj (D.host.conj (x : D.host.E)))).toCompletion
        rw [hcc]
      rw [MonoidHom.inv_apply, e1, hξ.2, hw₀, hcsd.1 _ _ hconj' x, inv_inv, hμ.2]
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer (maximalRealSubfield D.host.E) s.v
  set ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E) := (π : s.v.adicCompletion (maximalRealSubfield D.host.E)) with hϖdef
  have hϖ : Valued.v ϖ = WithZero.exp (-1) := by
    rw [hϖdef, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']; exact hπ
  have hϖ0 : ϖ ≠ 0 := by
    intro h0; rw [h0, map_zero] at hϖ; exact WithZero.zero_ne_coe hϖ
  let d : GL (Fin D.R.nV) (s.v.adicCompletion (maximalRealSubfield D.host.E)) :=
    ⟨Matrix.diagonal (fun a : Fin D.R.nV => if (a : ℕ) < D.R.r then 1 else ϖ),
     Matrix.diagonal (fun a : Fin D.R.nV => if (a : ℕ) < D.R.r then 1 else ϖ⁻¹),
     by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext a; split_ifs <;> simp [hϖ0],
     by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext a; split_ifs <;> simp [hϖ0]⟩
  obtain ⟨y, hyT, hyd⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq D.R.nV (GlobalTheory.TypeTame.conjSP s) d⁻¹
  obtain ⟨y0, hy0, hy00⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (D.naut.typeV_ne i Q)
  set f₀ := (P.M.loc i).real y0 with hf₀
  have hf0iso : f₀ ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q) := by
    rw [P.H.av.typeV] at hy0; exact hy0
  have hf0type : f₀ ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ := by
    rw [← (P.M.loc i).real_range]; exact LinearMap.mem_range_self _ _
  have hf0ne : f₀ ≠ 0 := fun h0 => hy00 ((P.M.loc i).real_inj (h0.trans (map_zero _).symm))
  refine ⟨NG.rt D.host.E D.R.nV y f₀, GlobalTheory.CompRed.isoTyp_stable _ _ _ hf0iso, ?_, ?_⟩
  · intro h0
    apply hf0ne
    funext g
    have := congrFun h0 (g * y⁻¹)
    simpa [NG.rt] using this
  · intro x hxT hxB
    have hv := _root_.GlobalTheory.SplitConjVal.valuation_eq s c hc hcs
    have hab := _root_.GlobalTheory.ConjLoc.loc_conjSP D.R.nV s x
    obtain ⟨κ, hκ⟩ : ∃ κ : GAf D.host.E D.R.nV, κ = y⁻¹ * x * y := ⟨_, rfl⟩
    have hκT : TrivOutside {s.v} κ := hκ ▸ GlobalTheory.TypeBlockConj.trivOutside_mul (GlobalTheory.TypeBlockConj.trivOutside_mul (GlobalTheory.TypeBlockConj.trivOutside_inv hyT) hxT) hyT
    have hκloc : (GlobalTheory.TypeTame.conjSP s).loc D.R.nV κ = d * (GlobalTheory.TypeTame.conjSP s).loc D.R.nV x * d⁻¹ := by
      rw [hκ, map_mul, map_mul, map_inv, hyd, inv_inv]
    obtain ⟨hUni, hsup⟩ := _root_.GlobalTheory.BlockConj.conj_transpose_inv_uniRT s D.R.r D.R.t c hv (s.loc D.R.nV x) ((GlobalTheory.TypeTame.conjSP s).loc D.R.nV x) hab hxB ϖ hϖ d rfl
    obtain ⟨u, hu, hbc⟩ := _root_.GlobalTheory.BlockConjDet.blockChar_eq_inv_detDD s D.R.r D.R.t c hv (s.loc D.R.nV x) ((GlobalTheory.TypeTame.conjSP s).loc D.R.nV x) hab hxB ϖ hϖ d rfl
    have hκJ : κ ∈ (P.M.loc i).J := (hU.mem κ hκT).2 (by rw [hκloc]; exact hUni)
    have hchr := hU.chr κ hκJ hκT u (by rw [hu, hκloc]; rfl)
    rw [hψ.1 _ (by rw [hκloc]; exact hsup), one_mul] at hchr
    have hty := hf0type.2 ⟨κ, hκJ⟩
    have hval : blockChar (S i s.w hw).mu (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) =
        (((P.M.loc i).χ ⟨κ, hκJ⟩ : ℂˣ) : ℂ) := by
      rw [hbc _ hμt, hchr, ← hrel u, MonoidHom.inv_apply, inv_inv]
    rw [hval]
    funext g
    have e := congrFun hty (g * y)
    have e2 : g * y * κ = g * x * y := by rw [hκ]; group
    rw [GlobalTheory.TypeBlockConj.rt_rt, Pi.smul_apply, ← e2]
    exact e
end GlobalTheory.TypeBlockConj
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PairReadOfJoin
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.PairReadPf
end GlobalTheory.PairReadPf
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.PairReadPf in
attribute [local instance] GlobalTheory.NPin.ThetaMod.acg GlobalTheory.NPin.ThetaMod.mod in
theorem GlobalTheory.NPin.pairRead_of_join_alt : GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), _root_.GlobalTheory.NPin.CharacterChoiceJoin P → ∀ S : Reading P.T, _root_.GlobalTheory.NPin.IsFaithfulReading P S → RowUnit S → PairRead S := by
  intro hBZ hL D P J S hT hRU i w hw σ Q hPairs
  obtain ⟨s, rfl⟩ := exists_splitPlace_w D w hw
  obtain ⟨j, hj⟩ : ∃ j : Fin D.R.m, j.1 + 1 = D.nd.j i :=
    ⟨⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩, by have := D.nd.j_range i; simp only; omega⟩
  obtain ⟨f, hf, F, hF, hne⟩ := hPairs
  have hFmem : (P.M.loc i).real F ∈ NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ := by
    have : (P.M.loc i).real F ∈ LinearMap.range (P.M.loc i).real := LinearMap.mem_range_self _ _
    rw [(P.M.loc i).real_range] at this
    exact this.1
  let X := J.rowM i
  let Θ := J.th i j hj
  let Fp : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ) := ⟨_, hFmem⟩
  let yp : ↥X.C := ⟨X.φ f, X.φ_mem f⟩
  have h0 : Θ.Λ Θ.φ₀ Fp yp ≠ 0 := by
    rw [← Θ.read F f Fp rfl]
    intro h
    apply hne
    show inner ℂ F (LinearMap.adjoint (D.what₂.thetaP (D.nd.mu i) (D.nd.j i)) f) = 0
    rw [LinearMap.adjoint_inner_right, ← inner_conj_symm, h, map_zero]
  have hμc := hT.mu i s.w hw j hj
  have hηc := hT.eta i s.w hw
  have hloc := Θ.loc s _ _ hμc hηc
  let ℓ0 : Θ.Ω →+ ℂ := AddMonoidHom.mk' (fun φ => Θ.Λ φ Fp yp) (by intro a b; simp)
  obtain ⟨ι, φ1, hφ1, hℓ1⟩ := exists_ne_of_mem_iSup _ ℓ0 hloc h0
  obtain ⟨hLin, φ2, ⟨Φ0, rfl⟩, hℓ2⟩ := exists_ne_of_mem_iSup _ ℓ0 hφ1 hℓ1
  obtain ⟨c, hc, hci, hιeq⟩ := hLin
  have hFiso : (Fp : GAf D.host.E D.R.nV → (P.M.loc i).wt.W) ∈
      NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q) := by
    have := hF
    rw [P.H.av.typeV] at this
    exact this
  have hspan := _root_.GlobalTheory.SpanLoc.main D.host.E D.R.nV (P.M.loc i).wt (P.H.av.S i Q) (P.H.av.irr i Q) s _
    (hT.rep i s hw Q) c hc hci
  let ℓF : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ) →+ ℂ :=
    AddMonoidHom.mk' (fun F' => Θ.Λ (ι Φ0) F' yp) (by intro a b; simp)
  obtain ⟨T1, F1, hF1, hℓF1⟩ := exists_ne_of_mem_iSup_sub _ _
    (fun T => iSup_le fun hT1 => by rintro _ ⟨v, rfl⟩; exact hT1.1 v) ℓF Fp (hspan hFiso) hℓ2
  obtain ⟨hT1, F2, ⟨a0, ha0⟩, hℓF2⟩ := exists_ne_of_mem_iSup_sub _ _
    (fun hT1 => by rintro _ ⟨v, rfl⟩; exact hT1.1 v) ℓF F1 hF1 hℓF1
  have hσne : D.what₂.isot (D.nd.j i) σ ≠ ⊥ := by
    intro hb
    rw [hb, Submodule.mem_bot] at hf
    subst hf
    exact hne (by simp)
  have hyI : (yp : X.A) ∈ Formalism.IndefR.principalLevelFrame.isotIn (D := D) X.ρ X.C (P.rep σ) := (X.isot σ f).1 hf
  unfold Formalism.IndefR.principalLevelFrame.isotIn at hyI
  let ℓy : ↥X.C →+ ℂ := (Θ.Λ (ι Φ0) F2).toAddMonoidHom
  obtain ⟨Φe, y1, hy1, hℓy1⟩ := exists_ne_of_mem_iSup_sub X.C _
    (fun Φe => iSup_le fun h => h.2) ℓy yp hyI hℓF2
  obtain ⟨hΦe, y2, ⟨f2, hf2⟩, hℓy2⟩ := exists_ne_of_mem_iSup_sub X.C _
    (fun h => h.2) ℓy y1 hy1 hℓy1
  have hΦC : ∀ g : ↥(P.rep σ).S, Φe g ∈ X.C := fun g => hΦe.2 (LinearMap.mem_range_self _ _)
  have hspan2 := _root_.GlobalTheory.FinTypSpanLoc.main D.host.E D.R.r (P.rep σ) s _ (hT.row i s hw σ hσne) c hc hci
  let ℓ2 : ↥(P.rep σ).S →+ ℂ :=
    AddMonoidHom.mk' (fun g => Θ.Λ (ι Φ0) F2 ⟨Φe g, hΦC g⟩) (by
      intro a b
      have e : (⟨Φe (a + b), hΦC (a + b)⟩ : ↥X.C) = ⟨Φe a, hΦC a⟩ + ⟨Φe b, hΦC b⟩ := by
        apply Subtype.ext; simp
      show Θ.Λ (ι Φ0) F2 ⟨Φe (a + b), hΦC (a + b)⟩ = Θ.Λ (ι Φ0) F2 ⟨Φe a, hΦC a⟩ + Θ.Λ (ι Φ0) F2 ⟨Φe b, hΦC b⟩
      rw [e, map_add (f := _)])
  have hℓ2f2 : ℓ2 f2 ≠ 0 := by
    have e : (⟨Φe f2, hΦC f2⟩ : ↥X.C) = y2 := Subtype.ext hf2
    show Θ.Λ (ι Φ0) F2 ⟨Φe f2, hΦC f2⟩ ≠ 0
    rw [e]; exact hℓy2
  obtain ⟨T2, g1, hg1, hℓg1⟩ := exists_ne_of_mem_iSup_sub _ _
    (fun T => iSup_le fun hT2 => by rintro _ ⟨v, rfl⟩; exact hT2.1 v) ℓ2 f2 (hspan2 f2.2) hℓ2f2
  obtain ⟨hT2, g2, ⟨c0, hc0⟩, hℓg2⟩ := exists_ne_of_mem_iSup_sub _ _
    (fun hT2 => by rintro _ ⟨v, rfl⟩; exact hT2.1 v) ℓ2 g1 hg1 hℓg1
  let T' : ((S i s.w hw).rep Q).V →ₗ[ℂ] ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ) :=
    T1.codRestrict _ hT1.1
  let T'' : ((S i s.w hw).row σ).V →ₗ[ℂ] ↥X.C :=
    (Φe ∘ₗ T2.codRestrict _ hT2.1).codRestrict X.C (fun v => hΦC _)
  have hT'eq : ∀ x : GAf D.host.E D.R.nV, TrivOutside {s.v} x → ∀ a,
      ((T' (((S i s.w hw).rep Q).π (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) a) :
        ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ)) : GAf D.host.E D.R.nV → (P.M.loc i).wt.W) =
        NG.rt D.host.E D.R.nV x (T' a : GAf D.host.E D.R.nV → (P.M.loc i).wt.W) :=
    fun x hx a => hT1.2 x hx a
  have hT''eq : ∀ x : GAf D.host.E D.R.r, TrivOutside {s.v} x → ∀ a,
      ((T'' (((S i s.w hw).row σ).π (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.r x)) a) : ↥X.C) : X.A) =
        X.ρ x (T'' a) := by
    intro x hx a
    have e : (⟨T2 (((S i s.w hw).row σ).π (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.r x)) a),
        hT2.1 _⟩ : ↥(P.rep σ).S) =
        ⟨NG.rt D.host.E D.R.r x (T2 a), (P.rep σ).stable x _ (hT2.1 a)⟩ := Subtype.ext (hT2.2 x hx a)
    show Φe ⟨_, _⟩ = X.ρ x (Φe ⟨T2 a, hT2.1 a⟩)
    rw [e]
    exact hΦe.1 x ⟨T2 a, hT2.1 a⟩
  let b := ((Θ.Λ ∘ₗ ι).compl₂ T').compr₂ (precompₛ T'')
  have hb0 : b Φ0 a0 c0 ≠ 0 := by
    have e1 : T' a0 = F2 := Subtype.ext ha0
    have e2 : T'' c0 = ⟨Φe g2, hΦC g2⟩ := by
      apply Subtype.ext
      show Φe ⟨T2 c0, hT2.1 c0⟩ = Φe g2
      congr 1
      exact Subtype.ext hc0
    show Θ.Λ (ι Φ0) (T' a0) (T'' c0) ≠ 0
    rw [e1, e2]
    exact hℓg2
  refine _root_.GlobalTheory.ThetaRiesz.thetaPair_of_invariant_form _ D.R.r (D.R.r + D.R.t) _ _ (S i s.w hw).mu ((S i s.w hw).row σ).π
    (twist ((S i s.w hw).rep Q).π (detChar (Fin (D.R.r + D.R.t)) (S i s.w hw).eta))
    ((hBZ _).1 (Fin D.R.r) _ _ ((S i s.w hw).row σ).smooth ((S i s.w hw).row σ).irr)
    (hRU i s.w hw σ hσne) (S i s.w hw).mu_ok.1 b (fun h => hb0 (by rw [h]; rfl)) ?_
  intro g h Φ Φ' hΦ a c'
  exact _root_.GlobalTheory.ThetaLocInv.thetaRead_inv D P.M i P.rep X _ _ Θ s (S i s.w hw).mu (S i s.w hw).eta ι c hιeq _ _
    ((S i s.w hw).rep Q).π ((S i s.w hw).row σ).π T' hT'eq T'' hT''eq g h Φ Φ' hΦ a c'
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PtSysFinite
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
noncomputable section
namespace GlobalTheory.SysFin
open GlobalTheory.CoefDuty
section Places
variable {R : Ranks} {H : Host R}
end Places
section Eig
variable {D : D7}
end Eig
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
open Classical in
theorem ptSys_finite_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ w : D.what₂.places.Pl, ∃ (F : Finset (PlE D.host)) (Sy : Finset (PlE D.host → ℕ → ℂ)), ∀ (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)) (Sp : NdSpec A.pl M C big L.X L.T), _root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation A M tp.tup Sp.iq L.Y L.C → ∀ (i : (withLoc L).nd.Loc) (x : (withLoc L).nd.X i), (withLoc L).nd.w i = w → ∃ c ∈ Sy, ∀ v, v ∉ F → ∀ k, GlobalTheory.CoefDuty.ptSys (withLoc L) i x v k = c v k := by
  intro D cf jE A low Pq S hL eig θ Bs M C tp hCh hMt hstar hexp hsplit hcheb w
  by_cases hw0 : D.what₂.muAt w = D.what₂.mu0
  · refine ⟨∅, ∅, fun big L Sp Au i x hi => absurd hw0 ?_⟩
    have := L.X.w_tw i
    rw [show L.X.w i = w from hi] at this
    exact this
  choose nq hnq0 hnqm using fun q : PlE D.host => exists_intCast_mem q
  set N : ℤ := (D.host.g 0 : ℤ) * (D.host.g 1 : ℤ) * (D.host.pde : ℤ) * (D.host.pde' : ℤ) * ∏ q ∈ C.Q w, nq q with hNdef
  have hN : N ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_) ?_
    · exact_mod_cast (D.host.g_prime 0).ne_zero
    · exact_mod_cast (D.host.g_prime 1).ne_zero
    · exact_mod_cast D.host.pde_prime.ne_zero
    · exact_mod_cast D.host.pde'_prime.ne_zero
    · exact Finset.prod_ne_zero_iff.2 fun q _ => hnq0 q
  have hfinN := finite_intCast_mem (K := D.host.E) N hN
  set F : Finset (PlE D.host) := hfinN.toFinset with hFdef
  have hF : ∀ v : PlE D.host, v ∉ F → (N : 𝓞 D.host.E) ∉ v.asIdeal := fun v hv h => hv (hfinN.mem_toFinset.2 h)
  set l := D.what₂.places.resChar w with hldef
  set Q' : Finset (PlE D.host) := C.Q w ∪ F with hQ'
  have hB : ∀ (j : Fin D.R.m) v k (s : SplitPlace D.host.E), GenAt D l Q' v k → IsConjPl D.host v s.w →
      s.v ∉ gPl D ∪ qPl D (tp.tup (D.what₂.muTw w) j) := by
    intro j v k s hg hc hs
    have hvF : v ∉ F := fun h => hg.2.2.2.1 (Finset.mem_union_right _ h)
    have key : ∀ (w' : PlE D.host) (n : ℤ), NG.OverPl w' s.v → n ∣ N → (n : 𝓞 D.host.E) ∉ w'.asIdeal := by
      intro w' n hov hd hn
      apply hF v hvF
      apply intCast_mem_of_dvd hd
      rw [intCast_mem_conj hc, intCast_mem_over s.w_under]
      exact (intCast_mem_over hov n).1 hn
    rcases hs with ⟨w', hov, k0, hk0⟩ | hq
    · refine key w' (D.host.g k0) hov ?_ (by exact_mod_cast hk0)
      fin_cases k0
      · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) _) _
      · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) _) _
    · obtain ⟨w', hov, hw'⟩ := GlobalTheory.FitHecke.qPl_sub tp w hw0 j hq
      rcases hw' with hQ | hp
      · exact key w' (nq w') hov (Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ hQ) _) (hnqm w')
      · split_ifs at hp
        · exact key w' D.host.pde' hov (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) (by exact_mod_cast hp)
        · exact key w' D.host.pde hov (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) _) (by exact_mod_cast hp)
  have hfin : ∀ j : Fin D.R.m, (EigSet (M (D.what₂.muTw w) (j.1 + 1) (by omega) (by omega)) l Q').Finite := fun j =>
    _root_.GlobalTheory.EigFinite.eigSet_finite _root_.GlobalTheory.HeckeStdFacts.heckeStdPlain D _ _ _ l Q' _ (hMt.hyp w j) (hB j)
  refine ⟨F, Finset.univ.biUnion fun j : Fin D.R.m => (hfin j).toFinset, fun big L Sp Au i x hi => ?_⟩
  obtain ⟨Hk, -⟩ := _root_.GlobalTheory.FitHecke.heckeOpen_withLoc_alt D cf jE A low Pq S hL eig θ Bs M C tp hCh hMt hstar hexp hsplit hcheb big L Sp Au
  have hpt := _root_.GlobalTheory.PointEigen.ptSys_mem_eigSet (withLoc L) (mtL L M) Hk.av i x
  have hwi : L.X.w i = w := hi
  have hl : L.X.l i = l := by rw [← L.X.w_l i, hwi]
  have hmem := GlobalTheory.FitHecke.mem_locs_self (D := withLoc L) i
  have hQ : L.X.Q i = C.Q w := by rw [← hwi]; exact (Sp.Q_eq _ _ i hmem).trans (Sp.Qc_eq _ _)
  have hj := L.X.j_range i
  let jf : Fin D.R.m := ⟨L.X.j i - 1, by omega⟩
  have hpt' : ptSys (withLoc L) i x ∈ EigSet (M (L.X.mu i) (L.X.j i) hj.1 hj.2) l (C.Q w) := by
    rw [← hl, ← hQ]; exact hpt
  have hpt'' := eigSet_transport M ((L.X.mu_w i).trans (by rw [hwi])) (show L.X.j i = jf.1 + 1 by simp [jf]; omega)
    hj.1 hj.2 (by omega) (by omega) l (C.Q w) _ hpt'
  refine ⟨fun v k => if GenAt D l Q' v k then ptSys (withLoc L) i x v k else 0, ?_, ?_⟩
  · refine Finset.mem_biUnion.2 ⟨jf, Finset.mem_univ _, (hfin jf).mem_toFinset.2 ?_⟩
    exact eigSet_restrict _ l Finset.subset_union_left hpt''
  · intro v hv k
    show _ = if GenAt D l Q' v k then _ else _
    split_ifs with hg
    · rfl
    · unfold ptSys
      rw [if_neg]
      intro hg'
      apply hg
      have hg2 : GenAt D l (C.Q w) v k := by rw [← hl, ← hQ]; exact hg'
      exact ⟨hg2.1, hg2.2.1, hg2.2.2.1, fun h => (Finset.mem_union.1 h).elim hg2.2.2.2.1 hv, hg2.2.2.2.2⟩
end GlobalTheory.SysFin
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RingSpecNormalisedCharacterEq
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.HeightCounting
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain _root_.Formalism.L2 Formalism.L2.NT
set_option synthInstance.maxHeartbeats 400000 in
structure NAllCAlt (D : D7) (C : NChoice D) where
  gal : _root_.Formalism.L2.NGalTiedAlt D
  n : _root_.GlobalTheory.HeightCounting.NTiedGPlaceholder D
  loc : LocTied D
  data : NormalizedDataCompatibility D
  cover : NormalizedLocalCompatibility D gal.mt
  chiD : NC.NChiData D
  chi : NC.NormalizedCharacterCompatibility D chiD
  rho : NR.NRhoTied D
  types : NormalizedTypesCompatibility D gal.fr.jE
  twF : TwFrame D
  tw : NTwTied D twF
  nct : NChTie D C
  exp : NExpTied D
  choice : ChoiceC D C
  eMt_level : ∀ (w : D.what₂.places.Pl) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
    (hw : TwistedAt D w) (hA : NX.AdmTw D (C.twI w) (C.k' w) (C.Q w) ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w)))),
    ∃ ι : FractionRing (C.Oe w) →+* ℂ, (∀ x : D.what₂.LL, ι (C.embW w x) = D.what₂.embLL x) ∧
      (gal.mt (D.what₂.muTw w) j h1 h2).J =
        (exp.mtV (C.twI w) j (C.sd w) (C.k' w) (C.Q w) ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w))) h1 h2 hA).J ∧
      ∀ (κ : Formalism.AUTREP.GAf D.host.E D.R.nV) (h : κ ∈ (gal.mt (D.what₂.muTw w) j h1 h2).J)
        (h' : κ ∈ (exp.mtV (C.twI w) j (C.sd w) (C.k' w) (C.Q w)
          ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w))) h1 h2 hA).J),
        (((gal.mt (D.what₂.muTw w) j h1 h2).χ ⟨κ, h⟩ : ℂˣ) : ℂ) =
          ι (C.kMapE w (((exp.mtV (C.twI w) j (C.sd w) (C.k' w) (C.Q w)
            ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w))) h1 h2 hA).χ ⟨κ, h'⟩ : (NX.Kk D (C.twI w) (C.k' w))ˣ) :
              NX.Kk D (C.twI w) (C.k' w)))
  cf : Host.CharFrame D
  tp : Host.TupTied D cf C
  tupLink : gal.TupLink tp
  eta_eq : ∀ x, chiD.etaT.χ x = cf.eta.1 x
  ringSpec_normalisedCharacter_eq : ∀ (j : Fin D.R.m) x, (chiD.mu0 (j.1 + 1)).χ x = (cf.mu0 j).1 x
  del_eq : ∀ s x, (chiD.del s).χ x = (cf.delAt (D.ntw.l s)).1 x
  psi_eq : ∀ a x, (chiD.psi a).χ x = (tp.psi (D.nd.w a)).1 x
  plB : D.what₂.places.Pl → ValuationSubring ℂ
  plκ : ∀ w, haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
    IsLocalRing.ResidueField (plB w) ≃+* Formalism.CyclotomicNorms.Fbar (D.what₂.places.resChar w)
  plB_loc : ∀ (i : D.nd.Loc) (y : D.nd.O i),
    haveI : Fact (D.what₂.places.resChar (D.nd.w i)).Prime := ⟨D.what₂.places.resChar_prime (D.nd.w i)⟩
    ∃ h : iotaOC D i y ∈ plB (D.nd.w i),
      Formalism.MainNotions.N.fbCast (D.nd.w_l i) (D.what₂.places.resChar_prime (D.nd.w i)) (D.nd.lPrime i).out
        (plκ (D.nd.w i) (IsLocalRing.residue (plB (D.nd.w i)) ⟨_, h⟩)) =
        D.naut.kFbar i (IsLocalRing.residue (D.nd.O i) y)
  plB_iota : ∀ (i : D.nd.Loc) k v x,
    haveI : Fact (D.what₂.places.resChar (D.nd.w i)).Prime := ⟨D.what₂.places.resChar_prime (D.nd.w i)⟩
    D.ntypes.iota k v (D.nd.w i) x = redThrough (plB (D.nd.w i)) (plκ (D.nd.w i)) (D.ntypes.teichC k x)
  etaT_link : ∀ (w : PlE D.host) (α : ℂ), chiD.etaT.At w α →
    D.naut.frobEig (D.naut.locG D.naut.etaT w) = {α⁻¹}
  muC_link : ∀ i : D.nd.Loc, ∀ᶠ w in Filter.cofinite, ∀ α : ℂ,
    (chiD.mu0 (D.nd.j i) * chiD.del (D.ntw.twOf i) * chiD.psi i).At w α →
    D.naut.frobEig (D.naut.locG (D.naut.muC i) w) = {α⁻¹}
  iCq_embO : ∀ s (x : ↥D.LL0), twF.iCq s (chiD.embO s true x) = D.what₂.embLL (x : D.what₂.LL)
  embO_star : ∀ s (x y : ↥D.LL0), (y : D.what₂.LL) = star (x : D.what₂.LL) → chiD.embO s false x = chiD.embO s true y
variable {D : D7} {C : NChoice D} {I : TwIn D}
end
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP _root_.Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain
def LpCmpAlt (_hL : _root_.UpperTheory.Zero.LLC.RecTExists) : Prop :=
  ∀ (D : D7) (_T : GlobalTheory.RowTie.WDTie D.nd D.naut), Nonempty (LPTiedPlaceholder D)
def CgCmpAlt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) : Prop :=
  ∀ (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut), _root_.GlobalTheory.HeightCounting.CGTrueT hL D T → Nonempty (_root_.GlobalTheory.HeightCounting.NTiedGPlaceholder D)
structure ArchimedeanComparison' (hL : _root_.UpperTheory.Zero.LLC.RecTExists) : Prop where
  pht : PhtCmp
  lp : _root_.GlobalTheory.HeightCounting.LpCmpAlt hL
  cg : _root_.GlobalTheory.HeightCounting.CgCmpAlt hL
end GlobalTheory.HeightCounting
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RingSpecNormalisedCharacterEqAlt
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain
open Formalism.L2.NT
namespace Formalism.L2
set_option synthInstance.maxHeartbeats 400000 in
structure NTiedAllAlt (D : D7) (C : NChoice D) (I : TwIn D) where
  gal : _root_.Formalism.L2.NGalTiedAlt D
  n : _root_.GlobalTheory.HeightCounting.NTiedGPlaceholder D
  loc : LocTied D
  data : NormalizedDataCompatibility D
  cover : NormalizedLocalCompatibility D gal.mt
  chiD : NC.NChiData D
  chi : NC.NormalizedCharacterCompatibility D chiD
  rho : NR.NRhoTied D
  types : NormalizedTypesCompatibility D gal.fr.jE
  twF : TwFrame D
  tw : NTwTied D twF
  nct : NChTie D C
  exp : NExpTied D
  choice : NChoiceTied D C I (avDesign D)
  eMt_level : ∀ (w : D.what₂.places.Pl) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
    (hw : TwistedAt D w) (hA : NX.AdmTw D (C.twI w) (C.k' w) (C.Q w) ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w)))),
    ∃ ι : FractionRing (C.Oe w) →+* ℂ, (∀ x : D.what₂.LL, ι (C.embW w x) = D.what₂.embLL x) ∧
      (gal.mt (D.what₂.muTw w) j h1 h2).J =
        (exp.mtV (C.twI w) j (C.sd w) (C.k' w) (C.Q w) ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w))) h1 h2 hA).J ∧
      ∀ (κ : Formalism.AUTREP.GAf D.host.E D.R.nV) (h : κ ∈ (gal.mt (D.what₂.muTw w) j h1 h2).J)
        (h' : κ ∈ (exp.mtV (C.twI w) j (C.sd w) (C.k' w) (C.Q w)
          ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w))) h1 h2 hA).J),
        (((gal.mt (D.what₂.muTw w) j h1 h2).χ ⟨κ, h⟩ : ℂˣ) : ℂ) =
          ι (C.kMapE w (((exp.mtV (C.twI w) j (C.sd w) (C.k' w) (C.Q w)
            ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w))) h1 h2 hA).χ ⟨κ, h'⟩ : (NX.Kk D (C.twI w) (C.k' w))ˣ) :
              NX.Kk D (C.twI w) (C.k' w)))
  cf : Host.CharFrame D
  tp : Host.TupTied D cf C
  tupLink : gal.TupLink tp
  eta_eq : ∀ x, chiD.etaT.χ x = cf.eta.1 x
  ringSpec_normalisedCharacter_eq : ∀ (j : Fin D.R.m) x, (chiD.mu0 (j.1 + 1)).χ x = (cf.mu0 j).1 x
  del_eq : ∀ s x, (chiD.del s).χ x = (cf.delAt (D.ntw.l s)).1 x
  psi_eq : ∀ a x, (chiD.psi a).χ x = (tp.psi (D.nd.w a)).1 x
  plB : D.what₂.places.Pl → ValuationSubring ℂ
  plκ : ∀ w, haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
    IsLocalRing.ResidueField (plB w) ≃+* Formalism.CyclotomicNorms.Fbar (D.what₂.places.resChar w)
  plB_loc : ∀ (i : D.nd.Loc) (y : D.nd.O i),
    haveI : Fact (D.what₂.places.resChar (D.nd.w i)).Prime := ⟨D.what₂.places.resChar_prime (D.nd.w i)⟩
    ∃ h : iotaOC D i y ∈ plB (D.nd.w i),
      fbCast (D.nd.w_l i) (D.what₂.places.resChar_prime (D.nd.w i)) (D.nd.lPrime i).out
        (plκ (D.nd.w i) (IsLocalRing.residue (plB (D.nd.w i)) ⟨_, h⟩)) =
        D.naut.kFbar i (IsLocalRing.residue (D.nd.O i) y)
  plB_iota : ∀ (i : D.nd.Loc) k v x,
    haveI : Fact (D.what₂.places.resChar (D.nd.w i)).Prime := ⟨D.what₂.places.resChar_prime (D.nd.w i)⟩
    D.ntypes.iota k v (D.nd.w i) x = redThrough (plB (D.nd.w i)) (plκ (D.nd.w i)) (D.ntypes.teichC k x)
  etaT_link : ∀ (w : PlE D.host) (α : ℂ), chiD.etaT.At w α →
    D.naut.frobEig (D.naut.locG D.naut.etaT w) = {α⁻¹}
  muC_link : ∀ i : D.nd.Loc, ∀ᶠ w in Filter.cofinite, ∀ α : ℂ,
    (chiD.mu0 (D.nd.j i) * chiD.del (D.ntw.twOf i) * chiD.psi i).At w α →
    D.naut.frobEig (D.naut.locG (D.naut.muC i) w) = {α⁻¹}
  iCq_embO : ∀ s (x : ↥D.LL0), twF.iCq s (chiD.embO s true x) = D.what₂.embLL (x : D.what₂.LL)
  embO_star : ∀ s (x y : ↥D.LL0), (y : D.what₂.LL) = star (x : D.what₂.LL) → chiD.embO s false x = chiD.embO s true y
end Formalism.L2
end
end
end

