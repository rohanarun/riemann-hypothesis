module

public import Mathlib
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.Bundle0001
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ProdMulLeDetIdeal
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ValuationLeOfEqAlgebraMap
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.AbsNormSpanGalois
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.Bundle0002
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ExistsEvalNeZeroOfTotalDegreeLt
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.FiniteDetAddSmulOneEqZero
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.LargeResidueExtensionLemma
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.HermitianFormGramBlockBasis
public import ReciprocityTheory.SemistableReduction.Bundle0008
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.KeyFormulaPowOfKeyFormula
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0118
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0037
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0039

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmPointLowerBoundFree
section
open NumberField IsDedekindDomain MeasureTheory IsLocalRing Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM
open scoped nonZeroDivisors ComplexOrder

namespace GlobalTheory

theorem cmPoint_lowerBound_free :
    ∀ (K : Type) [Field K] [NumberField K] (x : KeyIn K) (T abelian₂ : MLine K) (B : Type) [Fintype B] [DecidableEq B] (m : B → ℕ) (e : (Σ b, Fin (m b)) ≃ Fin x.P.g) (ℓ : Fin x.P.g → MLine K) (U : Matrix (Fin x.P.g) (Fin x.P.g) K) (G : MvPolynomial (FrVar m) K) (a : ∀ b, Fin (m b) → ℕ) (n r : ℕ) (La logOm : ℝ) (S : (K →+* ℂ) → ℝ), T.Good → abelian₂.Good → (∀ p, KeyLocAt x T abelian₂ p) → (∀ σ, KeyArchAt x T abelian₂ σ) → (∀ j, (ℓ j).Good) → (∀ j, (ℓ j).ndeg = logOm / 2) → U.det ≠ 0 → G ≠ 0 → 1 ≤ La → 1 ≤ r → (∀ b, m b ≤ r) → (∀ σ, 0 < S σ) → (∀ p, Step5Loc e T.dual abelian₂ ℓ U G n p) → (∀ σ, Step5Arch e T.dual abelian₂ ℓ U G a n La (S σ) σ) → - ((pDeg logOm + (1 / 2) * Real.log La) * (((∑ b, ∑ i, a b i : ℕ) : ℝ) + (x.P.g : ℝ) * n)) - ((∑ b, ∑ i, a b i : ℕ) : ℝ) * Real.log ((r : ℝ) * La) ≤ (∑ σ : K →+* ℂ, Real.log (S σ)) / (Module.finrank ℚ K : ℝ) :=
  _root_.GlobalTheory.cmLowerBound_of_coeffBound _root_.GlobalTheory.thetaDegree_and_lowerBound.2 ReciprocityTheory.MultiplicativeHeights.lemmaH_holds

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGoodCmPointOfIntegralCmObject
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT


set_option maxHeartbeats 1000000 in
theorem exists_cmPt_good_of_cmObj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (K : Type) [Field K] [NumberField K] [Algebra c.F K] (ρ : 𝓞 K) (σ : K →+* ℂ) (X : CMObj H K ρ σ Dw.p Dw.q) (La : ℝ) (x : Sp K ⟶ Xo.X) (Φ : FibKey Xo K x) (_ : SABMap Φ.T.t X.B.t (spMap (algebraMap (𝓞 K) K))), (∀ τ, τ ∈ LamF.psiSet H ↔ LamF.labK c K τ (H.rt : E) = (ρ : K)) → (∀ j (τ : E →+* ℂ), ‖τ (X.hh j : E)‖ ≤ La ^ 2) → x ≫ Xo.s = sOf c K → ∀ (S : Type) [CommRing S] [Algebra c.F S] (σ₁ : K →ₐ[c.F] S), ∃ (z : CMPt Xo c) (σ' : z.K →ₐ[c.F] S), z.Good (Module.finrank ℚ E / 2) La ∧ spMap σ'.toRingHom ≫ z.y.x = spMap σ₁.toRingHom ≫ x := by
  intro E _ _ _ H Dw l Xo c _ hstar K _ _ _ ρ σ X La x Φ m' hρ hLa hx S _ _ σ₁
  have hfib : LamF.IsFibreOf X.B.pol Φ.key (LamF.gmap K) m'.φ :=
    (LamF.isFibreOf_iff_isPolFibre (𝓞 K) K (algebraMap (𝓞 K) K) X.B.pol Φ.key m'.φ).2
      ((_root_.GlobalTheory.LamT.pat_pullback E H (𝓞 K) K (algebraMap (𝓞 K) K) X.B).2 Φ.T m' inferInstance).2.1
  obtain ⟨oa, oaΨ, oa', xΨ, x', φΨ, φ', τΨ, τ', ℓΨ, ℓ', Tl, LamL, hoa, -, -, hgood⟩ :=
    LamF.exists_lamObjGood_of_cmObj GlobalTheory.firstFiveLaws.2.1.secTwist GlobalTheory.thetaUnifAV_all GlobalTheory.firstFiveLaws.1
      GlobalTheory.homExtension_semiAbelian_dvr_unconditional E H l c hstar K ρ σ Dw.p Dw.q X La hρ hLa Φ.key m'.φ hfib
  obtain ⟨L, hL, hm⟩ := LamF.exists_lamLetters_isGood E H l c _ _ _ _ La hgood
  have hdet := LamF.Ind.lamInd E H l c hstar _ _ _ _ La hgood L hL
  have heig := LamF.LetterEigen.letter_eigen E H l c _ _ _ _ La hgood L hL
  obtain ⟨mm, e, src, U, ℓ⟩ := L
  have hmm : mm = Dw.mult := by
    funext b
    unfold Datum.mult
    split_ifs with h
    · exact (hm b).1 h
    · exact (hm b).2 h
  subst hmm
  choose w hw hU using hL.2.2.1
  obtain ⟨y, hy, htie, hu⟩ := _root_.GlobalTheory.LamT.exists_frPt_of_eigenbasis E H Dw l Xo c K x Φ e U w hx hdet hU (fun τ i =>
    _root_.GlobalTheory.LamT.isEigAt_of_model E H Dw l Xo c K x Φ.T.t X.B.t Φ.m m' τ (w (e ⟨τ, i⟩)) (fun a => by
      have h := heig τ i (w (e ⟨τ, i⟩)) (hw _) a
      rw [← hoa]
      exact h))
  refine ⟨CMPt.mk K x Φ X.B m' oa (X.A true).pol oaΨ (X.A false).pol oa' (fun i => X.φ (Sum.inl i))
    (fun i => X.φ (Sum.inr i)) (fun i => X.hh (Sum.inl i)) (fun i => X.hh (Sum.inr i)) xΨ x' φΨ φ' τΨ τ' ℓΨ ℓ' Tl LamL
    e src U ℓ y, σ₁, ⟨hgood, hL, hoa, hy, htie, fun τ i => ⟨w (e ⟨τ, i⟩), hw _, hu τ i⟩⟩, ?_⟩
  exact congrArg (fun t => spMap σ₁.toRingHom ≫ t) hy

end GlobalTheory.LamT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IntegralGeneratorAssociatedLocalGeneratorCMLine
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT.LocGen

theorem fibre_ne_of_generates {R : Type} [CommRing R] [IsLocalRing R] (P : Out.PolAV (Sp R)) (θ : P.L.Sec)
    (h : ∀ σ : P.L.Sec, ∃ c : ∀ i, Γ(P.A.left, P.L.U i), ∀ i, σ.f i = c i * θ.f i) (s : Sp R) :
    ∃ q : P.A.left, P.A.hom q = s ∧ q ∈ Out.nonzeroLocus θ := by
  have hT : Out.SecTwistSt := GlobalTheory.lawsFieldsSeparately.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hp : IsPullback (𝟙 P.A.left) P.A.hom P.A.hom (𝟙 _) := IsPullback.of_horiz_isIso ⟨by simp⟩
  obtain ⟨th, hth⟩ := KeyPow.exists_sec_fibre_ne_zero hT P hp
  obtain ⟨q, hq, hz⟩ := hth s
  obtain ⟨k, hk, u⟩ := (mem_nonzeroLocus _ _).1 hz
  obtain ⟨c, hc⟩ := h ⟨fun j => (P.A.left.presheaf.map (homOfLE (fun y hy => mem_pull.2 hy :
      P.L.U j ≤ (P.L.pull (𝟙 P.A.left)).U (fun _ => j))).op).hom (th.f fun _ => j), fun j j' => fn_ext fun y hy => by
    have h₁ : y ∈ (P.L.pull (𝟙 P.A.left)).U (fun _ => j) := mem_pull.2 hy.1
    have h₂ : y ∈ (P.L.pull (𝟙 P.A.left)).U (fun _ => j') := mem_pull.2 hy.2
    refine (gs_res _ y _ hy _).trans ((gs_res _ y _ hy.1 _).trans ((gs_compat th (𝟙 _) y h₁ h₂).trans
      (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) ((gs_unit _ y _ hy _).trans ?_)
        ((gs_res _ y _ hy _).trans (gs_res _ y _ hy.2 _)))))))
    rw [gm_pull_g P.L (𝟙 _) (𝟙 _) y _ _ h₁ h₂, Category.comp_id]⟩
  have hk' : q ∈ P.L.U (k PUnit.unit) := mem_pull.1 hk
  refine ⟨q, hq, (mem_nonzeroLocus _ _).2 ⟨_, hk', ?_⟩⟩
  have e := congrArg (gs (𝟙 _) q _) (hc (k PUnit.unit))
  rw [gs_mul _ q _ hk'] at e
  exact isUnit_of_mul_isUnit_right ((congrArg IsUnit ((gs_res (𝟙 _) q _ hk' _).symm.trans e)).mp u)

theorem isLieBasis_cast {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {n k : ℕ} (e : n = k)
    {v : Fin k → (epsR R ⟶ G)} (h : IsLieBasis v) : IsLieBasis fun i : Fin n => v (i.cast e) := by
  subst e; exact h

theorem isLieComb_cast {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {n k : ℕ} (e : n = k)
    (B : Matrix (Fin k) (Fin k) R) {v w : Fin k → (epsR R ⟶ G)} (h : ∀ i, IsLieComb (B i) v (w i)) (i : Fin n) :
    IsLieComb ((Matrix.of fun i j : Fin n => B (i.cast e) (j.cast e)) i) (fun i : Fin n => v (i.cast e))
      (w (i.cast e)) := by
  subst e; exact h i

theorem det_cast {R : Type} [CommRing R] {n k : ℕ} (e : n = k) (B : Matrix (Fin k) (Fin k) R) :
    (Matrix.of fun i j : Fin n => B (i.cast e) (j.cast e)).det = B.det := by
  subst e; rfl

theorem eps_sq {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') :
    spMap (Chart.dualMapR f) ≫ (epsR R).hom = (epsR R').hom ≫ spMap f := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

theorem stalk_of_isoMaps {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {w : LB.Iso L' (L.pull F)}
    {θ : L.Sec} {θ' : (L.pull F).Sec} {σ : L'.Sec} (h : IsoMaps w σ θ') (hθ : PullSec F θ θ')
    (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (j : L.ι) (k : L'.ι) (hj : F (r z) ∈ L.U j) (hk : r z ∈ L'.U k) :
    gs (r ≫ F) z _ (θ.f j) = (gw w r z j k).val * gs r z _ (σ.f k) := by
  have le : (L.pull F).U (fun _ => j) ≤ F ⁻¹ᵁ L.U j := fun q hq => mem_pull.1 hq
  rw [← (TieCalc.isoMaps_iff w σ θ').1 h Z r z j k hj hk, hθ (fun _ => j) le, gs_appLE F _ _ le r z (mem_pull.2 hj)]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem keyPB_of_sabMap {R R' : Type} [CommRing R] [CommRing R'] {f : R →+* R'} {T : PAT H (Sp R)} {T' : PAT H (Sp R')}
    (m : SABMap T'.t T.t (spMap f)) {w : LB.Iso T'.t.PP.L (T.t.PP.L.pull m.φ)} (hw : RigIso m w) (hg : T'.g = T.g)
    {g₀ th hth v hv g₀' th' hth' v' hv'}
    (hs : ∀ (Z : Scheme.{0}) (r : Z ⟶ T'.t.G.left) (z : Z) j k, m.φ (r z) ∈ T.t.PP.L.U j → r z ∈ T'.t.PP.L.U k →
      gs (r ≫ m.φ) z _ (LB.Sec.f th j) = (gw w r z j k).val * gs r z _ (LB.Sec.f th' k))
    (hl : ∀ i, (v' i).left ≫ m.φ = spMap (Chart.dualMapR f) ≫ (v (i.cast hg)).left) :
    KeyPB ⟨T'.pol, g₀', T'.t.PP.rig, T'.t.PP.rigGen, th', hth', v', hv'⟩
      ⟨T.pol, g₀, T.t.PP.rig, T.t.PP.rigGen, th, hth, v, hv⟩ f := by
  have he : eSec T'.t.G ≫ m.φ = spMap f ≫ eSec T.t.G := PolBaseChange.eSec_comm m.cart
  have hr := (maps_iff w _ (fun _ => eSec T.t.G) _ T'.t.PP.rig T.t.PP.rig m.cm.e _
    (rigPull_le m.cm.F m.cm.e m.cm.e_comm T.t.PP.L) (fun _ => rfl)).1 hw.2
  rw [m.base] at hr
  refine ⟨m.φ, he, w, hg, Chart.dualMapR f, m.cart, hw.1,
    (maps_iff w _ (fun _ => eSec T.t.G) _ T'.t.PP.rig T.t.PP.rig _ _ (rigPull_le m.φ _ he T.t.PP.L) (fun _ => rfl)).2 hr,
    KeyPow.appLE_eq_of_stalk _ th th' (hs _ (𝟙 _)), fun a => ?_, ?_, hl⟩
  · ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [Chart.dualMapR]

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}

theorem eq_mul_of_secTie {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S') {x x₀ : Sp S ⟶ Xo.X}
    {x₁ x₂ : Sp S' ⟶ Xo.X} {t : SAB H (Sp S)} {t' : SAB H (Sp S')} {m : SABMap t Xo.univ.t x}
    {m' : SABMap t' Xo.univ.t (spMap φ ≫ x)} {n : SABMap t' t (spMap φ)} (hφ : m'.φ = n.φ ≫ m.φ)
    {th : LB.Sec t.PP.L} {s₀ : LB.Sec (PPx x₀)} {s₁ : LB.Sec (PPx x₁)} {s₂ : LB.Sec (PPx x₂)} {a : S'}
    (e₀ : x₀ = x) (e₁ : x₁ = spMap φ ≫ x₀) (e₂ : x₂ = x₁) (h₀ : SecTie m th s₀) (b₁ : SecBC φ 1 x₀ x₁ s₀ s₁)
    (b₂ : SecBC (RingHom.id S') a x₁ x₂ s₁ s₂) {w : LB.Iso t'.PP.L (t.PP.L.pull n.φ)} (hw : RigIso n w)
    {th' σ : LB.Sec t'.PP.L}
    (hs : ∀ (Z : Scheme.{0}) (r : Z ⟶ t'.G.left) (z : Z) j k, n.φ (r z) ∈ t.PP.L.U j → r z ∈ t'.PP.L.U k →
      gs (r ≫ n.φ) z _ (th.f j) = (gw w r z j k).val * gs r z _ (th'.f k))
    (h₂ : SecTie m' σ s₂) : ∀ i, σ.f i = constFn t'.G.hom _ a * th'.f i := by
  subst e₀ e₁
  have h₁ : SecTie m' th' s₁ :=
    (TieCalc.secTie_baseChange m h₀ φ m' n s₁ w (thfPull _ n.φ th) th' rfl hφ b₁ hw (fun _ _ => rfl)).2
      ((TieCalc.isoMaps_iff w _ _).2 fun Z r z j k hj hk =>
        (gs_appLE n.φ _ _ _ r z (mem_pull.2 hj) _).trans (hs Z r z j k hj hk))
  exact ((TieCalc.secTie_calc E H Dw l Xo S' _ t' m' th' s₁ h₁).1 a x₂ s₂ σ e₂ b₂).1 h₂

theorem integral_generator_unit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La → ∀ (p : HeightOneSpectrum (𝓞 z.K)) (T : CDVR) (iK : z.K →+* T.Fr) (M : LocMod z T iK), (∀ y : z.K, iK y ∈ Set.range (algebraMap T.V T.Fr) ↔ p.valuation z.K y ≤ 1) → letI := (iK.comp (algebraMap c.F z.K)).toAlgebra; ∀ (φ : z.K →ₐ[c.F] T.Fr) (yT y' : FrPt Xo c T.Fr) (g : (∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) T.Fr)) (a : T.Fr), φ.toRingHom = iK → FrMap φ z.y yT → FrChg g a yT y' → SecInt T M.m1 M.m2 y'.s → ∀ ca : z.K, IsLocGen p ca z.Tl.I → ∃ u : T.Vˣ, a = iK ca * algebraMap T.V T.Fr u := by
  intro E _ _ _ H Dw l Xo c _ z f La hz p T iK M hT φ yT y' g a hφ hmap hchg hint ca hca
  obtain ⟨hobj, -, -, hx, htie, -⟩ := hz
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hloc, -, hmod⟩ := hobj
  obtain ⟨A, hA, hdet⟩ := hmod p
  obtain ⟨θ, hθ, w2, σ, θ2, r2, i2, p2, hσ⟩ := hint
  have hvV : ∃ vV : Fin z.Φ.T.g → (epsR T.V ⟶ M.G.t.G), IsLieBasis vV ∧ ∀ k, ∃ wK : epsR z.K ⟶ z.Φ.T.t.G, IsLieComb (A k) z.Φ.v wK ∧ spMap (Chart.dualMapR (algebraMap T.V T.Fr)) ≫ (vV k).left ≫ M.n.φ = spMap (Chart.dualMapR iK) ≫ wK.left ≫ z.m'.φ := by
    obtain ⟨R, _, _, _, _, _, ρ, xR, φR, hg, hρ, hR, ⟨hfib, -⟩, -, hv⟩ := hA
    have hinj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective _ _
    have exists_restrict_ringHom {R K V F : Type} [CommRing R] [CommRing K] [CommRing V] [CommRing F]
        (a : R →+* K) (b : V →+* F) (hb : Function.Injective b) (i : K →+* F)
        (h : ∀ r : R, i (a r) ∈ Set.range b) : ∃ ψ : R →+* V, b.comp ψ = i.comp a := by
      choose ψ hψ using h
      refine ⟨⟨⟨⟨ψ, hb ?_⟩, fun x y => hb ?_⟩, hb ?_, fun x y => hb ?_⟩, RingHom.ext fun r => hψ r⟩ <;> simp [hψ]
    obtain ⟨ψ, hψ⟩ := exists_restrict_ringHom (algebraMap R z.K) (algebraMap T.V T.Fr) hinj iK
      (fun r => (hT _).2 ((hR _).1 ⟨r, rfl⟩))
    have hρψ : M.ρ = ψ.comp ρ := by
      refine RingHom.ext fun x => hinj ?_
      have h₁ := RingHom.congr_fun M.hρ x
      have h₂ := RingHom.congr_fun hψ (ρ x)
      have h₃ := RingHom.congr_fun hρ x
      simp only [RingHom.comp_apply] at h₁ h₂ h₃ ⊢
      rw [h₁, h₂, h₃]
    have hp : IsGrpPullback xR.P.A z.B.t.G (spMap ρ) φR := hfib
    have e : spMap M.ρ = spMap ψ ≫ spMap ρ := by rw [hρψ]; exact spMap_comp ρ ψ
    have hn : IsGrpPullback M.G.t.G z.B.t.G (spMap M.ρ) M.n.φ := M.n.cart
    have w : M.n.φ ≫ z.B.t.G.hom = (M.G.t.G.hom ≫ spMap ψ) ≫ spMap ρ := by rw [hn.1.w, e, Category.assoc]
    have hq : IsGrpPullback M.G.t.G xR.P.A (spMap ψ) (hp.1.lift _ _ w) :=
      IsGrpPullback.cancel hp (hn.congr e (hp.1.lift_fst _ _ w).symm) (hp.1.lift_snd _ _ w)
    have := xR.P.isAb.comm
    obtain ⟨v', hb, hv'⟩ := GlobalTheory.exists_isLieBasis_baseChange R T.V ψ _ _ _ hq xR.P.isAb.smooth _ xR.v xR.basis
    have hb' : ∀ (k : ℕ) (hk : xR.P.g = k), IsLieBasis fun i : Fin k => v' (i.cast hk.symm) := by
      rintro k rfl
      exact hb
    refine ⟨fun k => v' (k.cast hg.symm), hb' _ hg, fun k => ?_⟩
    obtain ⟨wK, hw, hw'⟩ := hv k
    refine ⟨wK, hw, ?_⟩
    have ed : (Chart.dualMapR (algebraMap T.V T.Fr)).comp (Chart.dualMapR ψ) =
        (Chart.dualMapR iK).comp (Chart.dualMapR (algebraMap R z.K)) := by
      refine RingHom.ext fun x => ?_
      have h₁ := RingHom.congr_fun hψ x.fst
      have h₂ := RingHom.congr_fun hψ x.snd
      simp only [RingHom.comp_apply] at h₁ h₂
      refine TrivSqZeroExt.ext ?_ ?_
      · simpa [Chart.dualMapR, Chart.dualMapR] using h₁
      · simp only [Chart.dualMapR, Chart.dualMapR, RingHom.comp_apply, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
          TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
        exact h₂
    have es : spMap (Chart.dualMapR (algebraMap T.V T.Fr)) ≫ spMap (Chart.dualMapR ψ) =
        spMap (Chart.dualMapR iK) ≫ spMap (Chart.dualMapR (algebraMap R z.K)) := by
      rw [← spMap_comp, ← spMap_comp, ed]
    have e₁ : (v' (k.cast hg.symm)).left ≫ M.n.φ =
        spMap (Chart.dualMapR ψ) ≫ (xR.v (k.cast hg.symm)).left ≫ φR := by
      rw [← Category.assoc, ← hv', Category.assoc, hp.1.lift_fst]
    exact (congrArg (_ ≫ ·) e₁).trans <| (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) es).trans <|
      (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hw'.symm)
  obtain ⟨vV, bV, hV⟩ := hvV
  obtain ⟨g1, -, w1, r1⟩ := (pat_pullback E H _ _ iK z.Φ.T).2 M.t' M.n' inferInstance
  obtain ⟨g2, -⟩ := (pat_pullback E H _ _ (algebraMap T.V T.Fr) M.G).2 M.t' M.m2 inferInstance
  have g3 : M.G.g = z.Φ.T.g := g2.symm.trans g1
  obtain ⟨th', hth'⟩ := sec_pull_down ((isGen_iff _).1 r1.1) z.Φ.T.t.PP.isLB M.t'.t.PP.isLB z.Φ.th
  have nz' := SectionBaseChange.fibre_nonzero_of_pull M.t'.t.PP.isLB hth' M.n'.cart.1 z.Φ.th_ne
  have nzθ := fibre_ne_of_generates M.G.pol θ fun τ => (hθ τ).exists.elim fun b hb => ⟨_, hb⟩
  have hσθ := stalk_of_isoMaps i2 p2
  have nzσ := SectionBaseChange.fibre_nonzero_of_pull M.t'.t.PP.isLB hσθ M.m2.cart.1 nzθ
  obtain ⟨v0, b0, h0⟩ := GlobalTheory.exists_isLieBasis_baseChange _ _ iK _ _ _ M.n'.cart z.Φ.T.ab.smooth _ z.Φ.v z.Φ.basis
  obtain ⟨v1, b1, h1⟩ := GlobalTheory.exists_isLieBasis_baseChange _ _ (algebraMap T.V T.Fr) _ _ _ M.m2.cart M.G.ab.smooth _ vV bV
  have hc : ∀ k, IsLieComb (iK.mapMatrix A k) v0 (v1 k) := fun k => by
    show IsLieComb (fun j => iK (A k j)) v0 (v1 k)
    obtain ⟨wK, hw, hw'⟩ := hV k
    refine Chart.comb_baseChange iK M.n'.cart hw h0 (z.m'.cart.1.hom_ext ?_ ?_)
    · rw [Category.assoc, Category.assoc, ← M.h2, ← Category.assoc, h1, Category.assoc]
      exact hw'
    · rw [Category.assoc, Category.assoc, M.n'.cart.1.w, ← Category.assoc, Over.w, Over.w, eps_sq]
  have hσa : ∀ i, σ.f i = constFn M.t'.t.G.hom _ a * th'.f i := by
    obtain ⟨e₁, -, pm, ps, pf, hp⟩ := hmap
    rw [hφ] at e₁ pf
    refine eq_mul_of_secTie iK M.h1 hx e₁ hchg.1 htie ⟨pm, ps, pf, fun i h => ?_⟩ hchg.2.2 r1 hth' hσ
    rw [SecCalc.scal_one' z.y.x i, _root_.one_mul]
    exact hp i h
  have gp : 1 ≤ M.t'.g := g1 ▸ z.Φ.g_pos
  let x' : KeyIn T.Fr := ⟨M.t'.pol, gp, M.t'.t.PP.rig, M.t'.t.PP.rigGen, th', nz', _, isLieBasis_cast g1 b0⟩
  let xR : KeyIn T.V := ⟨M.G.pol, gp.trans g2.le, M.G.t.PP.rig, M.G.t.PP.rigGen, θ, nzθ, _, isLieBasis_cast g3 bV⟩
  have k1 : KeyPB x' z.Φ.key iK := keyPB_of_sabMap M.n' r1 g1 hth' fun i => h0 _
  have k2 : KeyPB ⟨M.t'.pol, gp, M.t'.t.PP.rig, M.t'.t.PP.rigGen, σ, nzσ, _, isLieBasis_cast g1 b1⟩ xR
      (algebraMap T.V T.Fr) := keyPB_of_sabMap M.m2 r2 g2 hσθ fun i => h1 _
  have k3 : KeyIntegral T.V x' a (iK A.det) :=
    ⟨σ, nzσ, _, isLieBasis_cast g1 b1, Matrix.of fun i j => iK.mapMatrix A (i.cast g1) (j.cast g1), xR, hσa,
      isLieComb_cast g1 (iK.mapMatrix A) hc, (det_cast g1 _).trans (RingHom.map_det iK A).symm, k2⟩
  exact KeyVal.integral_section_unit z.K z.Φ.key z.Tl z.LamL p (hloc p) T.V T.Fr iK x' a (iK A.det) ca A.det 1 hT
    k1 k3 hdet (by rw [Units.val_one, map_one, _root_.mul_one]) hca

end GlobalTheory.LamT.LocGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MetricDataUnique
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT.MetUniq

theorem uniq_cast (x : KeyIn ℂ) (g : ℕ) (hg : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (Hm : Matrix (Fin g) (Fin g) ℂ)
    (χ : u.Λ → ℂ) (θ : (Fin g → ℂ) → ℂ) (Fd : Set (Fin g → ℂ)) (u' : HolUnif x.P.A x.P.L x.P.g)
    (Hm' : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (χ' : u'.Λ → ℂ) (θ' : (Fin x.P.g → ℂ) → ℂ) (Fd' : Set (Fin x.P.g → ℂ))
    (h : u.IsAH Hm χ ∧ u.IsRig x.rig ∧ u.IsFn x.th θ ∧ IsAddFundamentalDomain u.Λ Fd volume)
    (h' : u'.IsAH Hm' χ' ∧ u'.IsRig x.rig ∧ u'.IsFn x.th θ' ∧ IsAddFundamentalDomain u'.Λ Fd' volume) :
    (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) / (volume Fd).toReal =
      (∫ z in Fd', ‖θ' z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm' z z).re)) / (volume Fd').toReal ∧
    ∀ (v w : epsR ℂ ⟶ x.P.A) (V W : Fin g → ℂ) (V' W' : Fin x.P.g → ℂ), IsTangent v → IsTangent w → u.IsDiff V v →
      u.IsDiff W w → u'.IsDiff V' v → u'.IsDiff W' w → hermForm Hm V W = hermForm Hm' V' W' := by
  subst hg
  exact _root_.GlobalTheory.KeyUniq.norm_eq_and_hermForm_eq x u Hm χ θ Fd u' Hm' χ' θ' Fd' h h'

theorem spMap_dualMap_id (S : Type) [CommRing S] :
    spMap (Formalism.L2.Pj.dualMap (RingHom.id S)) = 𝟙 (Sp (DualNumber S)) := by
  have : Formalism.L2.Pj.dualMap (RingHom.id S) = RingHom.id _ := by
    refine RingHom.ext fun r => ?_
    ext <;> simp [Formalism.L2.Pj.dualMap]
  rw [this]
  exact Spec.map_id _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}

theorem isMetricAt_unique (x : Sp ℂ ⟶ Xo.X) (s : LB.Sec (PPx x))
    (uu : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)) (ht : ∀ τ i, IsTanAt x (uu τ i))
    (N N' : ℝ) (Gr Gr' : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) ℂ)
    (h : IsMetricAt x s uu N Gr) (h' : IsMetricAt x s uu N' Gr') : N = N' ∧ Gr = Gr' := by
  obtain ⟨Φ, u, Hm, χ, θ, Fd, w, W, tie, a1, a2, a3, a4, hN, hw, hG⟩ := h
  obtain ⟨Φ', u', Hm', χ', θ', Fd', w', W', tie', b1, b2, b3, b4, hN', hw', hG'⟩ := h'
  have hx : x = spMap (RingHom.id ℂ) ≫ x := by
    have : spMap (RingHom.id ℂ) = 𝟙 (Sp ℂ) := Spec.map_id _
    rw [this, Category.id_comp]
  have sc := GlobalTheory.Frames.SecCalc.sec_calc E H Dw l Xo ℂ ℂ ℂ (RingHom.id ℂ) (RingHom.id ℂ) x x x hx hx
  have hbc : SecBC (RingHom.id ℂ) 1 x x s s := (sc.2.1 1 s s).2 fun i => by
    rw [(sc.2.2.2 1 1 i).2.2, _root_.one_mul]
  obtain ⟨hg, v', hv', kp, hv⟩ := GlobalTheory.T.universalTripleFibreKeyData_baseChange_keyPullback E H Dw l Xo ℂ ℂ (RingHom.id ℂ) x x Φ Φ' s s hx tie tie' hbc
  simp only [spMap_dualMap_id, Category.id_comp] at hv
  obtain ⟨u₁, χ₁, θ₁, Fd₁, c1, c2, c3, c4, hN₁, hD⟩ := _root_.GlobalTheory.KeyTransport.uniformisation_transport Φ.key _ kp hg _ u Hm χ θ Fd ⟨a1, a2, a3, a4⟩
  have hm : Hm.map (RingHom.id ℂ) = Hm := rfl
  rw [hm] at c1 hN₁
  obtain ⟨e1, e2⟩ := uniq_cast ({ Φ' with v := v', basis := hv' } : FibKey Xo ℂ x).key _ hg u₁ Hm χ₁ θ₁ Fd₁
    u' Hm' χ' θ' Fd' ⟨c1, c2, c3, c4⟩ ⟨b1, b2, b3, b4⟩
  have tan : ∀ b i, IsTangent (G := Φ.T.t.G) (w b i) := fun b i =>
    (Chart.tan_push Φ.m.cart _).2 (((congrArg (_ ≫ ·) (hw b i).1)).trans (ht b i).2)
  have tan' : ∀ b i, IsTangent (G := Φ'.T.t.G) (w' b i) := fun b i =>
    (Chart.tan_push Φ'.m.cart _).2 (((congrArg (_ ≫ ·) (hw' b i).1)).trans (ht b i).2)
  have key : ∀ b i, u₁.IsDiff (W b i) (w' b i) := fun b i => by
    obtain ⟨cf, hcf, -⟩ := Φ.basis.2 (w b i) (tan b i)
    refine hD cf (w b i) (w' b i) (W b i) hcf ?_ (hw b i).2
    obtain ⟨p, hp, hq⟩ := (Chart.comb_push Φ.m.cart _ _ _).1 hcf
    refine (Chart.comb_push Φ'.m.cart _ v' (w' b i)).2 ⟨fun j => p (j.cast hg), fun j => ?_, ?_⟩
    · exact (hp _).trans (congrArg (_ ≫ ·) (hv j).symm)
    · have : List.ofFn (fun j : Fin Φ'.T.g => p (j.cast hg)) = List.ofFn p := (List.ofFn_congr hg.symm p).symm
      exact (congrArg (fun L => (List.prod L).left) this).trans (hq.trans ((hw b i).1.trans (hw' b i).1.symm))
  refine ⟨hN.trans (hN₁.symm.trans (e1.trans hN'.symm)), ?_⟩
  funext b
  ext i k
  rw [hG, hG', e2 (w' b k) (w' b i) _ _ _ _ (tan' b k) (tan' b i) (key b k) (key b i) (hw' b k).2 (hw' b i).2]

theorem isMetric_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (y : FrPt Xo c (CAt σ)) (N N' : ℝ) (Gr Gr' : (∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) ℂ)), IsMetric y N Gr → IsMetric y N' Gr' → N = N' ∧ Gr = Gr' :=
  fun _ _ _ _ _ _ _ _ _ _ y N N' Gr Gr' h h' => isMetricAt_unique y.x y.s y.u y.tan N N' Gr Gr' h h'

end GlobalTheory.LamT.MetUniq
end

