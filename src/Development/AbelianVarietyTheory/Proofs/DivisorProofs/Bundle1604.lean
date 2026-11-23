module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0026
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CuspFormsVanishingOffFramesLeSpanShortTheta
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0038
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0057
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1512
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1583
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1559
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1563
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1570
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1586
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1582
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1547
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1543
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0763
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetGaussianEntireOriginGridFrames
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0066

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolSub0LeSpanRaw
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RawSpan

section Cover

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

abbrev idCover (nab : NabV Xo c) (n : ℕ) : DeltaDat Xo c n := noDelta Xo c nab (GlobalTheory.ObjLower.sabId Xo.univ.t) n

theorem frOver_self (nab : NabV Xo c) (n : ℕ) {S : Type} [CommRing S] [i : Algebra c.F S] (y : FrPt Xo c S) :
    @FrOver E _ _ _ H Dw l Xo c n (idCover nab n) S _ i i y y := by
  refine (@GlobalTheory.FrameLift.frOver_iff E _ _ _ H Dw l Xo S _ c n (idCover nab n) i i y y).2
    ⟨Category.comp_id _, fun _ _ => Category.comp_id _, GlobalTheory.ObjLower.idIso Xo.univ.t.PP.L, 𝟙 _,
      ⟨(isGen_iff _).2 (GlobalTheory.ObjLower.pgen_idIso Xo.univ.t.PP.isLB), ?_⟩,
      (Category.id_comp _).trans (Category.comp_id _).symm, Category.id_comp _, ?_⟩
  · exact (maps_iff (GlobalTheory.ObjLower.idIso Xo.univ.t.PP.L) _ (fun _ => eSec Xo.univ.t.G) _ Xo.univ.t.PP.rig
      Xo.univ.t.PP.rig (GlobalTheory.ObjLower.cubeId Xo.univ.t.G).e _
      (rigPull_le (GlobalTheory.ObjLower.cubeId Xo.univ.t.G).F (GlobalTheory.ObjLower.cubeId Xo.univ.t.G).e
        (GlobalTheory.ObjLower.cubeId Xo.univ.t.G).e_comm Xo.univ.t.PP.L) (fun _ => rfl)).2
      (GlobalTheory.ObjLower.pmaps_idIso _ _ _ _ Xo.univ.t.PP.rigGen)
  · intro Z r z i j hi hj
    have e := GlobalTheory.ObjLower.gw_idIso Xo.univ.t.PP.L (r ≫ (snd (Over.mk y.x) Xo.univ.t.G).left) z i j hi hj
    have e' := GlobalTheory.FrameLift.sv_trans (q := (snd (Over.mk y.x) Xo.univ.t.G).left) y.s r z hi hj
    exact (congrArg (fun t => GlobalTheory.FrameLift.sv (q := (snd (Over.mk y.x) Xo.univ.t.G).left) y.s t z i)
      (Category.comp_id r)).trans (e'.trans (congrArg (fun u : (Z.presheaf.stalk z)ˣ => u.val * _) e.symm))

theorem evR_one_field (S : Type) [Field S] [Algebra c.F S] (y : FrPt Xo c S) : evR Xo c 1 y = 1 :=
  evalAt_one _ _ y (GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.firstFiveLaws.1.secBaseChange E H Dw l Xo c S y)

theorem idCover_isLev (nab : NabV Xo c) (n : ℕ) : (idCover nab n).IsLev := by
  refine ⟨⟨dvd_rfl, le_rfl, dvd_rfl⟩, (Nat.mul_one _).symm, Nat.coprime_one_left _, (Ideal.mul_top _).symm,
    top_sup_eq _, ?_, ?_, GlobalTheory.LevelCover.one_mem_sec_zero Xo c, ?_⟩
  · rw [GlobalTheory.LevelCoverDatum.noDelta_etaOK]
    exact ⟨fun a => Category.comp_id _, fun a => Category.comp_id _⟩
  · intro k _ _ i₁ i₂ hk y
    have e : i₂ = i₁ := Algebra.algebra_ext _ _ fun a => hk a
    rw [e]
    exact ⟨y, @frOver_self E _ _ _ H Dw l Xo c nab n k _ i₁ y⟩
  · intro k _ _ i y₂
    have := @evR_one_field E _ _ _ H Dw l Xo c k _ i y₂
    exact fun h => one_ne_zero (this.symm.trans h)

theorem idCover_unitC (nab : NabV Xo c) (n : ℕ) : GlobalTheory.Dict.UnitC (idCover nab n) := fun A y =>
  (congrArg norm (@evR_one_field E _ _ _ H Dw l Xo c ℂ _ A y)).trans norm_one

theorem idCover_psiTie (nab : NabV Xo c) (n : ℕ) : (idCover nab n).PsiTie 1 := by
  intro k g ρ _ _ _ _ K _ _ i y y' _
  have a := @evR_one_field E _ _ _ H Dw l Xo c K _ i y
  have b := @evR_one_field E _ _ _ H Dw l Xo c K _ i y'
  refine b.trans ?_
  refine Eq.symm ((congrArg _ a).trans ?_)
  simp

theorem betaH_ne_zero {n : ℕ} (Λ : GenLat E n) : betaH (Dw := Dw) c Λ ≠ 0 := by
  unfold betaH
  split_ifs with h
  · exact h.choose_spec.1
  · exact one_ne_zero

theorem phiHat_indPhi_mk {n : ℕ} (x0 : Fin n → Dw.La) :
    phiHat c (indPhi c fun b => (Submodule.Quotient.mk (x0 b) : LevQc Dw l)) = x0Dat c x0 := by
  have h : phiHat c (indPhi c fun b => (Submodule.Quotient.mk (x0 b) : LevQc Dw l)) =
      x0Dat c fun b => qRep (Submodule.Quotient.mk (x0 b) : LevQc Dw l) := by
    funext q
    unfold phiHat x0Dat indPhi
    rw [finsum_eq_single _ (fun b => (Submodule.Quotient.mk (x0 b) : LevQc Dw l)) (fun x hx => by simp [hx])]
    simp
  rw [h, GlobalTheory.LevelPairing.levelFourierDatum_eq_iff]
  intro b
  exact (Submodule.Quotient.eq _).1 (Classical.choose_spec (Submodule.Quotient.mk_surjective _
    (Submodule.Quotient.mk (x0 b) : LevQc Dw l)))

theorem span_mk_eq_top {n : ℕ} (x0 : Fin n → Dw.La) (h : AdmX (l := l) true x0) :
    Submodule.span (𝓞 E) (Set.range fun b => (Submodule.Quotient.mk (x0 b) : LevQc Dw l)) = ⊤ := by
  unfold AdmX at h
  rw [sup_comm, ← Submodule.map_mkQ_eq_top, Submodule.map_span, Set.image_image] at h
  rw [← h]
  congr 1
  ext z
  simp

theorem thLaValAt_of_isShortRule [StarRing (𝓞 E)] (nab : NabV Xo c) (hnab : IsNab Xo c nab) {n : ℕ} {Λ : GenLat E n} {N : ℕ}
    (hU : Λ.Unimod) (hT : Λ.TrivAt l.M) (hO : Λ.LevOK N l.M) {a : (E →+* ℂ) × ℕ → ℕ}
    {P : MvPolynomial (LtN Dw n) c.F} (hP : P ∈ harmL c Λ a) (x0 : Fin n → Dw.La) {f : Rul Xo c}
    (hf : f ∈ sec Xo c a n) (h : IsShortRule Xo c (idCover nab n) Λ N x0 P f) (p : TRing c.F) (y : FrPt Xo c p.R) :
    thLaValAt Xo c nab (x0Dat c x0) Λ N P y ((betaH (Dw := Dw) c Λ • f) p y) := by
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  haveI : _root_.IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced p.I).1 p.rad
  obtain ⟨hval, hnat⟩ := GlobalTheory.shortThetaValue_existsUnique_natural hL GlobalTheory.chartIndependence_unconditional E H Dw l Xo c
    nab hnab n Λ N hU hT hO a P hP.1 (x0Dat c x0) (betaH (Dw := Dw) c Λ)
  obtain ⟨v, hv, -⟩ := hval p.R y
  have e : f p y = v := by
    refine GlobalTheory.CoverDescent.eq_of_geometric_points _ _ fun k _ _ χ => ?_
    letI i1 : Algebra c.F k := (χ.comp (algebraMap c.F p.R)).toAlgebra
    let χa : p.R →ₐ[c.F] k := { χ with commutes' := fun _ => rfl }
    obtain ⟨z, hz⟩ := GlobalTheory.FramedBaseChange.exists_frMap hL E H Dw l Xo c p.R k χa y
    obtain ⟨u, hu, eu⟩ := @h k _ _ i1 i1 (fun _ => rfl) z z (frOver_self nab n z)
    have hu' : ShortValAt Xo c nab (x0Dat c x0) Λ (betaH (Dw := Dw) c Λ) N P z u := by
      have e1 : MvPolynomial.map ((idCover nab n).eF : c.F →+* (idCover nab n).c₂.F) P = P := MvPolynomial.map_id P
      rw [e1, GlobalTheory.LevelCoverDatum.noDelta_w] at hu
      exact hu
    have e2 := hnat p.R k χa y z hz v u hv hu'
    have e3 := GlobalTheory.CoverDescent.evR_of_test (GlobalTheory.Frames.algebraic_laws hL.secBaseChange E H Dw l Xo c).2.2.1 f hf.1
      p χa y z hz
    have e4 : evR Xo c f z = u := eu.trans ((congrArg (· * u) (evR_one_field k z)).trans (_root_.one_mul u))
    exact e3.symm.trans (e4.trans e2.symm)
  have e5 : (betaH (Dw := Dw) c Λ • f) p y = algebraMap c.F p.R (betaH (Dw := Dw) c Λ) * v := by
    rw [← e]
    exact Algebra.smul_def (betaH (Dw := Dw) c Λ) (f p y)
  rw [e5]
  exact (GlobalTheory.Survey.BaseClassMove.shortValAt_beta Xo c nab _ Λ _ (betaH_ne_zero Λ) N P y v).1 hv

end Cover

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor


set_option maxHeartbeats 1000000 in
theorem holSub0_le_span_raw : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.Pj.Unf Xo c σ r), Formalism.L2.Pj.GoodEmb c σ → Formalism.L2.Pj.IsUnf U → 1 ≤ r → l.A = 1 → (∀ k k', (U.X k).Gm = (U.X k').Gm ∧ (U.X k).ξ0 = (U.X k').ξ0) → (∀ k, GlobalTheory.Dict.HasPrinc (U.X k) l.M) → ∀ [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (bad n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ), 0 < bad → Dom a n → 4 * (Module.finrank ℚ E * r) + 4 ≤ n → (∀ k, GlobalTheory.Dict.ChiOne (U.X k) (Formalism.L2.Pj.laU U a n k)) → Formalism.L2.Pj.holSub0 U.X (Formalism.L2.Pj.laU U a n) ≤ Submodule.span ℂ (Formalism.L2.Pj.rdU U '' ⋃ (x0 : Fin n → LevQc Dw l) (_ : Submodule.span (𝓞 E) (Set.range x0) = ⊤), {f : Formalism.L2.Pj.Rul Xo c | f ∈ sec Xo c a n ∧ ∃ (La : GenLat E n) (N : ℕ) (P : MvPolynomial (LtN Dw n) c.F), La.Unimod ∧ La.TrivAt bad ∧ La.TrivAt l.M ∧ La.LevOK N l.M ∧ P ∈ harmL c La a ∧ ∀ (p : TRing c.F) (y : FrPt Xo c p.R), thLaValAt Xo c nab (phiHat c (indPhi c x0)) La N P y (f p y)}) := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU hr hA hG hP _ nab hnab bad n a hbad hdom hn hχ
  have hC := GlobalTheory.chartIndependence_unconditional
  have hrk : r = Dw.p + Dw.q := hU.1
  have h1 : 1 ≤ Dw.p + Dw.q := hrk ▸ hr
  have hL : Out.Laws := GlobalTheory.firstFiveLaws.1
  have hB : Out.SecBaseChangeSt := hL.secBaseChange
  have hpin := GlobalTheory.DeltaPinTest.noDelta_phiPin (n := n) nab (GlobalTheory.ObjLower.sabId Xo.univ.t)
  have hT := GlobalTheory.Frames.allTest_of_secBaseChange hB E H Dw l Xo c
  have hW := (GlobalTheory.Frames.algebraic_laws hB E H Dw l Xo c).2.2.1
  have htot : ShortValTot Xo c nab bad n a n (idCover nab n) :=
    GlobalTheory.shortValTot_of_pinned hL hC E H Dw l Xo c n (idCover nab n) (GlobalTheory.levelMaps_closed hL E H Dw h1) hW hT hW hT
      (idCover_isLev nab n) rfl ⟨_, hnab⟩ (fun _ => ⟨_, 1, _, hpin, idCover_psiTie nab n⟩) nab bad n a
  have key := GlobalTheory.Dict.holSub0_le_span_shortGen hC E H Dw l Xo c n (idCover nab n) σ r
    (Formalism.L2.PjFree.Unf.ofPj U) hσ hU hr hA hG hP (idCover_isLev nab n) ⟨_, hnab⟩ (idCover_unitC nab n)
    (by show ¬ 3 ∣ 1; decide) (fun _ => ⟨_, 1, _, hpin⟩) nab bad n a hbad hdom hn hχ htot
  intro Q hQ
  refine Submodule.span_le.2 ?_ (key hQ)
  rintro _ ⟨f, ⟨hf, Λ, N, x0, P, hΛ, hb, hM, hO, hX, hPm, hrule⟩, rfl⟩
  have hβ := betaH_ne_zero (Dw := Dw) (c := c) Λ
  have e : Formalism.L2.PjFree.rdU (Formalism.L2.PjFree.Unf.ofPj U) f =
      (σ (betaH (Dw := Dw) c Λ))⁻¹ • Formalism.L2.Pj.rdU U (betaH (Dw := Dw) c Λ • f) := by
    rw [LinearMap.map_smulₛₗ, smul_smul, inv_mul_cancel₀ ((map_ne_zero σ).2 hβ), one_smul]
    rfl
  rw [e]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ?_, rfl⟩)
  rw [decide_eq_true (rfl : n = n)] at hX
  refine Set.mem_iUnion₂.2 ⟨fun b => Submodule.Quotient.mk (x0 b), span_mk_eq_top x0 hX,
    Submodule.smul_mem _ _ hf, Λ, N, P, hΛ, hb, hM, hO, hPm, fun p y => ?_⟩
  rw [phiHat_indPhi_mk]
  exact thLaValAt_of_isShortRule nab hnab hΛ hM hO hPm x0 hf hrule p y

end GlobalTheory.RawSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndexIdealRankOneTensorImageEqMap
section
set_option autoImplicit false

noncomputable section

open NumberField

namespace GlobalTheory.IdxTensor
theorem cut_idxmap : ∀ {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V]
    [IsScalarTower (𝓞 F) F V] (p : ℕ) (φ : (Fin p → F) →ₗ[F] V), Function.Injective φ →
    ∀ (L N : Submodule (𝓞 F) (Fin p → F)),
    GlobalTheory.FlatCM.idx F p (L.map (φ.restrictScalars (𝓞 F))) (N.map (φ.restrictScalars (𝓞 F))) =
      (GlobalTheory.IdxTensor.dets F p N).colon (GlobalTheory.IdxTensor.dets F p L : Set F) := _root_.GlobalTheory.IdxMap.idx_map_eq_colon_dets

theorem cut_detsspan : ∀ {F : Type} [Field F] [NumberField F] (p : ℕ) (S : Set (Fin p → F)),
    GlobalTheory.IdxTensor.dets F p (Submodule.span (𝓞 F) S) =
      Submodule.span (𝓞 F) {d | ∃ y : Fin p → Fin p → F, (∀ i, y i ∈ S) ∧ d = (Matrix.of y).det} := _root_.GlobalTheory.IdxTensor.dets_span_eq

theorem cut_rankone : ∀ {K : Type} [Field K] [NumberField K] {m : ℕ} (ell : Submodule (𝓞 K) (Fin m → K)),
    ReciprocityTheory.GeometryOfNumbersTheory.latRank K ell = 1 → ell.FG →
    ∃ v : Fin m → K, v ≠ 0 ∧ ∃ 𝔟 : Submodule (𝓞 K) K, 𝔟.FG ∧ 𝔟 ≠ ⊥ ∧
      ∀ e, e ∈ ell ↔ ∃ β ∈ 𝔟, e = β • v := _root_.GlobalTheory.latRank_one_eq_ideal_smul

theorem cut_linindep : ∀ {K : Type} [Field K] [NumberField K] {p m n : ℕ} (ell : Submodule (𝓞 K) (Fin m → K))
    (M : Fin p → ((Fin m → K) →ₗ[K] (Fin n → K))) (v : Fin m → K), v ≠ 0 → ∀ (𝔟 : Submodule (𝓞 K) K),
    𝔟 ≠ ⊥ → (∀ e, e ∈ ell ↔ ∃ β ∈ 𝔟, e = β • v) → (∀ a, Function.Injective (M a)) →
    iSupIndep (fun a => Submodule.span K
      ((ell.map ((M a).restrictScalars (𝓞 K)) : Submodule (𝓞 K) (Fin n → K)) : Set (Fin n → K))) →
    LinearIndependent K (fun a => M a v) := _root_.GlobalTheory.linearIndependent_images_of_rankOne_lattice

theorem cut_cancel : ∀ {K : Type} [Field K] [NumberField K] (𝔟 : Submodule (𝓞 K) K), 𝔟.FG → 𝔟 ≠ ⊥ →
    ∀ (p : ℕ) (A N : Submodule (𝓞 K) K),
    (𝔟 ^ p * N).colon ((𝔟 ^ p * A : Submodule (𝓞 K) K) : Set K) = N.colon (A : Set K) := GlobalTheory.T.colon_pow_mul_cancel_fg_fractional

theorem cut_extend : ∀ {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K]
    (τ : 𝓞 E →+* 𝓞 K) (τE : E →+* K), (∀ x : 𝓞 E, τE x = ((τ x : 𝓞 K) : K)) →
    ∀ (A : Submodule (𝓞 E) E), A.FG → (1 : E) ∈ A →
    (1 : Submodule (𝓞 K) K).colon (Submodule.span (𝓞 K) (τE '' A) : Set K) =
      ((1 : Submodule (𝓞 E) E).colon (A : Set E)).map τ := GlobalTheory.T.colon_one_span_image_eq_map_colon

theorem cut_twistgens : ∀ {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K]
    (τ : 𝓞 E →+* 𝓞 K) (τE : E →+* K), (∀ x : 𝓞 E, τE x = ((τ x : 𝓞 K) : K)) → ∀ (p : ℕ)
    (𝔟 : Submodule (𝓞 K) K) (Λ : Submodule (𝓞 E) (Fin p → E)),
    Submodule.span (𝓞 K) {d | ∃ y : Fin p → Fin p → K,
        (∀ i, y i ∈ {x : Fin p → K | ∃ β ∈ 𝔟, ∃ c ∈ Λ, x = β • fun a => τE (c a)}) ∧ d = (Matrix.of y).det} =
      𝔟 ^ p * Submodule.span (𝓞 K) (τE '' GlobalTheory.IdxTensor.dets E p Λ) := GlobalTheory.T.span_scaled_mapped_row_dets_eq_pow_mul_span

theorem span_image_one {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K]
    (τ : 𝓞 E →+* 𝓞 K) (τE : E →+* K) (hτ : ∀ x : 𝓞 E, τE x = ((τ x : 𝓞 K) : K)) :
    Submodule.span (𝓞 K) (τE '' (1 : Submodule (𝓞 E) E)) = 1 := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro x ⟨y, hy, rfl⟩
    obtain ⟨z, rfl⟩ := Submodule.mem_one.1 hy
    exact Submodule.mem_one.2 ⟨τ z, (hτ z).symm⟩
  · rw [Submodule.one_le]
    apply Submodule.subset_span
    exact ⟨1, Submodule.mem_one.2 ⟨1, map_one _⟩, map_one τE⟩

theorem one_mem_dets {F : Type} [Field F] [NumberField F] (p : ℕ) (L : Submodule (𝓞 F) (Fin p → F))
    (h : ∀ a, (Pi.single a (1 : F) : Fin p → F) ∈ L) : (1 : F) ∈ dets F p L := by
  unfold dets
  apply Submodule.subset_span
  refine ⟨fun a => Pi.single a 1, h, ?_⟩
  have hI : Matrix.of (fun a : Fin p => (Pi.single a (1 : F) : Fin p → F)) = 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [Pi.single_apply, Matrix.one_apply, hij, Ne.symm hij]
  rw [hI, Matrix.det_one]

theorem dets_std {F : Type} [Field F] [NumberField F] (p : ℕ) :
    dets F p (Submodule.span (𝓞 F) (Set.range fun a => (Pi.single a (1 : F) : Fin p → F))) = 1 := by
  rw [cut_detsspan]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro d ⟨y, hy, rfl⟩
    choose f hf using fun i => Set.mem_range.1 (hy i)
    have hM : Matrix.of y =
        (Matrix.of fun i j => (Pi.single (f i) (1 : 𝓞 F) : Fin p → 𝓞 F) j).map (algebraMap (𝓞 F) F) := by
      ext i j
      simp only [Matrix.of_apply, Matrix.map_apply]
      rw [← hf i]
      by_cases hij : j = f i
      · subst hij; simp
      · simp [Pi.single_apply, hij]
    rw [hM]
    exact Submodule.mem_one.2 ⟨_, RingHom.map_det _ _⟩
  · rw [Submodule.one_le]
    apply Submodule.subset_span
    refine ⟨fun a => Pi.single a 1, fun i => ⟨i, rfl⟩, ?_⟩
    have hI : Matrix.of (fun a : Fin p => (Pi.single a (1 : F) : Fin p → F)) = 1 := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp
      · simp [Pi.single_apply, Matrix.one_apply, hij, Ne.symm hij]
    rw [hI, Matrix.det_one]

theorem big_eq_map {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] (τE : E →+* K) {p m n : ℕ}
    (ell : Submodule (𝓞 K) (Fin m → K)) (M : Fin p → ((Fin m → K) →ₗ[K] (Fin n → K)))
    (Λ : Submodule (𝓞 E) (Fin p → E)) (v : Fin m → K) (𝔟 : Submodule (𝓞 K) K)
    (hell : ∀ e, e ∈ ell ↔ ∃ β ∈ 𝔟, e = β • v) :
    Submodule.span (𝓞 K) {w | ∃ c ∈ Λ, ∃ e ∈ ell, w = ∑ a, τE (c a) • M a e} =
      (Submodule.span (𝓞 K) {x | ∃ β ∈ 𝔟, ∃ c ∈ Λ, x = β • fun a => τE (c a)}).map
        ((Fintype.linearCombination K (fun a => M a v)).restrictScalars (𝓞 K)) := by
  rw [Submodule.map_span]
  congr 1
  ext w
  constructor
  · rintro ⟨c, hc, e, he, rfl⟩
    obtain ⟨β, hβ, rfl⟩ := (hell e).1 he
    refine ⟨β • fun a => τE (c a), ⟨β, hβ, c, hc, rfl⟩, ?_⟩
    rw [LinearMap.coe_restrictScalars, Fintype.linearCombination_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Pi.smul_apply, map_smul, smul_smul, smul_eq_mul, mul_comm]
  · rintro ⟨x, ⟨β, hβ, c, hc, rfl⟩, rfl⟩
    refine ⟨c, hc, β • v, (hell _).2 ⟨β, hβ, rfl⟩, ?_⟩
    rw [LinearMap.coe_restrictScalars, Fintype.linearCombination_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Pi.smul_apply, map_smul, smul_smul, smul_eq_mul, mul_comm]

private lemma sum_single_smul_eq_apply {E K : Type} [Field E] [Field K] (τE : E →+* K) {p m n : ℕ}
    (M : Fin p → ((Fin m → K) →ₗ[K] (Fin n → K))) (b : Fin p) (e : Fin m → K) :
    ∑ a, τE ((Pi.single b (1 : E) : Fin p → E) a) • M a e = M b e := by
  rw [Finset.sum_eq_single b]
  · simp
  · intro a _ hab
    simp [Pi.single_apply, hab]
  · simp

theorem small_eq_big_std {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K]
    (τ : 𝓞 E →+* 𝓞 K) (τE : E →+* K) (hτ : ∀ x : 𝓞 E, τE x = ((τ x : 𝓞 K) : K)) {p m n : ℕ}
    (ell : Submodule (𝓞 K) (Fin m → K)) (M : Fin p → ((Fin m → K) →ₗ[K] (Fin n → K))) :
    (⨆ a, ell.map ((M a).restrictScalars (𝓞 K))) =
      Submodule.span (𝓞 K) {w | ∃ c ∈ Submodule.span (𝓞 E) (Set.range fun a => (Pi.single a (1 : E) : Fin p → E)),
        ∃ e ∈ ell, w = ∑ a, τE (c a) • M a e} := by
  apply le_antisymm
  · refine iSup_le fun b => ?_
    rintro w ⟨e, he, rfl⟩
    exact Submodule.subset_span
      ⟨Pi.single b 1, Submodule.subset_span ⟨b, rfl⟩, e, he, (sum_single_smul_eq_apply τE M b e).symm⟩
  · rw [Submodule.span_le]
    rintro w ⟨c, hc, e, he, rfl⟩
    induction hc using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      beta_reduce
      rw [sum_single_smul_eq_apply τE M b e]
      exact Submodule.mem_iSup_of_mem b ⟨e, he, rfl⟩
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [Pi.add_apply, map_add (f := _), add_smul, Finset.sum_add_distrib]
      exact add_mem hx hy
    | smul r x _ hx =>
      have key : ∀ a, τE ((r • x) a) • M a e = τ r • (τE (x a) • M a e) := by
        intro a
        rw [Pi.smul_apply, Algebra.smul_def r (x a), map_mul, mul_smul, ← algebraMap_smul K (τ r)]
        congr 1
        exact hτ r
      rw [Finset.sum_congr rfl (fun a _ => key a), ← Finset.smul_sum]
      exact Submodule.smul_mem _ _ hx

theorem dets_fg {F : Type} [Field F] [NumberField F] (p : ℕ) (L : Submodule (𝓞 F) (Fin p → F)) (h : L.FG) :
    (dets F p L).FG := by
  obtain ⟨S, rfl⟩ := h
  rw [cut_detsspan]
  apply Submodule.fg_span
  refine ((Set.Finite.pi (fun _ : Fin p => S.finite_toSet)).image
    (fun y : Fin p → Fin p → F => (Matrix.of y).det)).subset ?_
  rintro d ⟨y, hy, rfl⟩
  exact ⟨y, fun i _ => hy i, rfl⟩

theorem dets_twist {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K]
    (τ : 𝓞 E →+* 𝓞 K) (τE : E →+* K) (hτ : ∀ x : 𝓞 E, τE x = ((τ x : 𝓞 K) : K)) (p : ℕ)
    (𝔟 : Submodule (𝓞 K) K) (Λ : Submodule (𝓞 E) (Fin p → E)) :
    dets K p (Submodule.span (𝓞 K) {x | ∃ β ∈ 𝔟, ∃ c ∈ Λ, x = β • fun a => τE (c a)}) =
      𝔟 ^ p * Submodule.span (𝓞 K) (τE '' dets E p Λ) := by
  rw [cut_detsspan]
  exact cut_twistgens τ τE hτ p 𝔟 Λ

theorem idx_image_eq_map : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] (τ : 𝓞 E →+* 𝓞 K) (τE : E →+* K),
    (∀ x : 𝓞 E, τE x = ((τ x : 𝓞 K) : K)) → ∀ (p m n : ℕ) (ell : Submodule (𝓞 K) (Fin m → K))
    (M : Fin p → ((Fin m → K) →ₗ[K] (Fin n → K))) (Λ : Submodule (𝓞 E) (Fin p → E)),
    ell.FG → ReciprocityTheory.GeometryOfNumbersTheory.latRank K ell = 1 → (∀ a, Function.Injective (M a)) →
    iSupIndep (fun a => Submodule.span K ((ell.map ((M a).restrictScalars (𝓞 K)) : Submodule (𝓞 K) (Fin n → K)) : Set (Fin n → K))) →
    Λ.FG → (∀ x : Fin p → 𝓞 E, (fun a => (x a : E)) ∈ Λ) →
    GlobalTheory.FlatCM.idx K p (Submodule.span (𝓞 K) {w | ∃ c ∈ Λ, ∃ e ∈ ell, w = ∑ a, τE (c a) • M a e})
                 (⨆ a, ell.map ((M a).restrictScalars (𝓞 K))) =
      (GlobalTheory.FlatCM.idx E p Λ (Submodule.span (𝓞 E) (Set.range fun a => (Pi.single a (1 : E) : Fin p → E)))).map τ := by
  intro E K _ _ _ _ τ τE hτ p m n ell M Λ hfg hrk hinj hind hΛfg hΛ
  obtain ⟨v, hv, 𝔟, h𝔟fg, h𝔟, hell⟩ := cut_rankone ell hrk hfg
  have hφ : Function.Injective (Fintype.linearCombination K (fun a => M a v)) :=
    (cut_linindep ell M v hv 𝔟 h𝔟 hell hinj hind).fintypeLinearCombination_injective
  have hsing : ∀ a, (Pi.single a (1 : E) : Fin p → E) ∈ Λ := by
    intro a
    have h1 := hΛ (Pi.single a 1)
    convert h1 using 1
    funext b
    by_cases hab : b = a
    · subst hab; simp
    · simp [Pi.single_apply, hab]
  have hD1 : (1 : E) ∈ GlobalTheory.IdxTensor.dets E p Λ := one_mem_dets p Λ hsing
  have hDfg : (GlobalTheory.IdxTensor.dets E p Λ).FG := dets_fg p Λ hΛfg
  have hR := cut_idxmap (V := Fin p → E) p (LinearMap.id) Function.injective_id Λ
    (Submodule.span (𝓞 E) (Set.range fun a => (Pi.single a (1 : E) : Fin p → E)))
  have hmapid : ∀ L : Submodule (𝓞 E) (Fin p → E),
      L.map ((LinearMap.id : (Fin p → E) →ₗ[E] (Fin p → E)).restrictScalars (𝓞 E)) = L := by
    intro L
    ext x
    simp
  rw [hmapid, hmapid] at hR
  rw [hR, small_eq_big_std τ τE hτ ell M, big_eq_map τE ell M Λ v 𝔟 hell, big_eq_map τE ell M _ v 𝔟 hell,
    cut_idxmap p _ hφ, dets_twist τ τE hτ, dets_twist τ τE hτ, dets_std, span_image_one τ τE hτ,
    cut_cancel 𝔟 h𝔟fg h𝔟 p _ 1]
  exact cut_extend τ τE hτ _ hDfg hD1

end GlobalTheory.IdxTensor

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralInjectiveSubspaceCompactOpenConstNeZeroStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_injectiveSubspace_compactOpen_const_ne_zero : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (κ : Type) [Fintype κ],
    ∀ (N : ℕ) (ν : @Measure (Fin N → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
    ∀ j : (Fin N → Fv F v) →ₗ[Fv F v] (κ → Fv F v) × (κ → Fv F v), Function.Injective j →
    ∀ c : ℂ, c ≠ 0 → ∀ U : Set ((κ → Fv F v) × (κ → Fv F v)), IsOpen U → IsCompact U → 0 ∈ U →
    ∫ y, U.indicator (fun _ => c) (j y) ∂ν ≠ 0 := by
  first | exact @GlobalTheory.integral_indicator_preimage_injective_ne_zero | exact GlobalTheory.integral_indicator_preimage_injective_ne_zero | (intros; apply GlobalTheory.integral_indicator_preimage_injective_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralPointsIndicatorFourierSelfUnramifiedStatement
section
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralPointsIndicator_fourier_self_unramified : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (ψ : AddChar (Fv F v) ℂ),
    (∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, ψ (x * y) = 1) ↔ x ∈ v.adicCompletionIntegers F) → ∀ (κ : Type) [Fintype κ]
    [MeasurableSpace (κ → Fv F v)] [BorelSpace (κ → Fv F v)] (μ : Measure (κ → Fv F v)) [μ.IsAddHaarMeasure],
    μ {x | ∀ i, x i ∈ v.adicCompletionIntegers F} = 1 → (fun y : κ → Fv F v => ∫ x, ind κ v x * ψ (x ⬝ᵥ y) ∂μ) = ind κ v := by
  first | exact @GlobalTheory.RatWeilOp.ind_fourier_self | exact GlobalTheory.RatWeilOp.ind_fourier_self | (intros; apply GlobalTheory.RatWeilOp.ind_fourier_self <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualCColumnLatticeOfOrthonormalFrame
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FunObj.OrthoFrame

theorem isSelfDualC_colLat_of_orthonormal : ∀ {D : D7} (S : HSp D) (B : GL (Fin S.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B.1 * S.gram * B.1 = 1 → IsSelfDualC S (colLat B) := by
  intro D S B hB
  exact GlobalTheory.FunObj.VecEx.isSelfDualC_colLat S B hB

end GlobalTheory.FunObj.OrthoFrame
end
end

