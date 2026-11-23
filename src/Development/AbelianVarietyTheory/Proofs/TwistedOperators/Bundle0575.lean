module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0573
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0308
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0332
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0519
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0377
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0408
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0065
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.BaseIntSet
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0902
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0253
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0234
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0365
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0349
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0407
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0411
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0746
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle0005
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0001
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0008
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AlgebraicDataUnitaryRelationsFinitePlacePolZeroStatement
section
open NumberField IsDedekindDomain
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicData_unitaryRelations_finitePlace_polZero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf → ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), ∀ g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ G.V (GlobalTheory.AdelicU.evFin F v),
    ∀ Φ ∈ GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb, GlobalTheory.PolKer.PolZero Bs G Xc R Rf (om (g, 1) Φ - Φ) := by
  first | exact @GlobalTheory.PolKer.polZero_relV | exact GlobalTheory.PolKer.polZero_relV | (intros; apply GlobalTheory.PolKer.polZero_relV <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodGivesFourierJacobiPeriodOfLift
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.UpFromBessel

variable {D : D7}

theorem pair_self_ne_zero {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    (v : VolM D T.rank S.rank) {f₀ : WO S T → ℂ} (hf : IsThetaFunO ψ S T f₀) (hne : f₀ ≠ 0) :
    thPair v.μ v.𝓕 f₀ f₀ ≠ 0 := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.MixModel.lattice_Mx D T.rank S.rank
  haveI : BorelSpace (Mx D T.rank S.rank) := ⟨rfl⟩
  haveI : DiscreteTopology (ratMx D T.rank S.rank) := i5
  haveI : Countable (ratMx D T.rank S.rank) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  obtain ⟨hμ, hF, h1⟩ := v.covol
  haveI := hμ
  haveI : IsFiniteMeasure (v.μ.restrict v.𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
  obtain ⟨C, hC⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ hf
  have e : ∀ w, f₀ w * star (f₀ w) = ((‖f₀ w‖ ^ 2 : ℝ) : ℂ) := fun w => by
    rw [Complex.star_def, Complex.mul_conj']; push_cast; rfl
  have hint : Integrable (fun w => ‖f₀ w‖ ^ 2) (v.μ.restrict v.𝓕) :=
    Integrable.of_bound (hf.cont.norm.pow 2).measurable.aestronglyMeasurable (C ^ 2)
      (Filter.Eventually.of_forall fun w => by
        rw [Real.norm_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hC w) 2)
  intro h0
  have h2 : (∫ w in v.𝓕, ‖f₀ w‖ ^ 2 ∂v.μ) = 0 := by
    have : thPair v.μ v.𝓕 f₀ f₀ = ((∫ w in v.𝓕, ‖f₀ w‖ ^ 2 ∂v.μ : ℝ) : ℂ) := by
      unfold thPair
      simp_rw [e]
      exact integral_ofReal
    rw [this] at h0
    exact_mod_cast h0
  have h3 : ∫⁻ w in v.𝓕, ‖f₀ w‖ₑ ^ 2 ∂v.μ = 0 := by
    have en : ∀ z : ℂ, ‖z‖ₑ ^ 2 = ENNReal.ofReal (‖z‖ ^ 2) := fun z => by
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
    simp_rw [en]
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun w => by positivity), h2,
      ENNReal.ofReal_zero]
  exact hne (GlobalTheory.OrientedHeis.eq_zero_of_lintegral_eq_zero (ratMx D T.rank S.rank) v.μ v.𝓕 hF f₀ hf.cont
    (fun γ hγ w => GlobalTheory.OrientedHeis.theta_norm_periodic hψ hf γ hγ w) h3)

theorem per_smul {ρ : ℕ} (B : BesL D ρ) (ψ : AddChar (AF D.host.F) ℂ) (c : ℂ) (φ : GA D B.A → ℂ) (f : GA D B.V → ℂ) :
    B.per ψ (c • φ) f = c * B.per ψ φ f := by
  simp only [BesL.per, besPer, besFun, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]

theorem upFB : ∀ D : D7, UpFB D := by
  intro D ψ σ J B s 𝒮 Γ₀ K hL χA χz omb omz hχ hb hz φ G hφ hG hK Ξ₁ Φ₀ hΞ hΦ hne hvac hper
  by_contra hcon
  push_neg at hcon
  have hψ := s.weil.std
  obtain ⟨vL⟩ := (GlobalTheory.Unf.VolExist.measures_exist D).2.2.1 B.L.rank J.W₀.rank
  have hvan := GlobalTheory.T.vanishing_descends_fourierJacobi_to_bessel D ψ σ J B s 𝒮 Γ₀ K hL vL _ _ omz hz φ G Φ₀ hφ hG hΦ hK hcon
  have htame := _root_.GlobalTheory.HandTame.handP₂ D ψ σ J B s vL _ _ omz hz φ G Φ₀ hφ hG hΦ
  obtain ⟨Φ, hΦS, hfl⟩ := hL.ne
  have hall := _root_.GlobalTheory.Irr.irr D ψ hψ J.W₀ B.V₀ Γ₀ _ htame _ (hL.vac Φ hΦS) hfl (fun w hw => by
    have h1 := (GlobalTheory.FlatHeis.flatAt_heisO D ψ hψ J.W J.W₀ B.V B.V₀ (σ + 1) σ J.d B.d s.vS s.vT s.vU
      (xLast B.d (vecB B.o B.ζ)) 0 Φ (hL.theta Φ hΦS)).2.1 w
    have h2 := hvan _ (hL.core Φ hΦS w hw)
    simp only [flFB, flatS] at h2 ⊢
    rw [h1] at h2
    exact h2) _ hvac
  have hlink := _root_.GlobalTheory.HandProd.handP_boxT D ψ σ J B s vL χA χz omb omz hχ hb hz φ Ξ₁ Φ₀ Φ₀ hΞ hΦ hΦ
  simp only [hlink, per_smul] at hall
  exact hper ((mul_eq_zero.1 hall).resolve_left (pair_self_ne_zero hψ vL hΦ hne))

end GlobalTheory.UpFromBessel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenFixTranslates
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open Formalism.IndefR.NX (ExpSet CoefLat)
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.Tow

open scoped Topology

noncomputable section

namespace GlobalTheory.VacTranslate

variable {D : D7}

theorem exists_finCong_mod (V W : HSp D) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (hV : IsSelfDualC V ΛV) (hW : IsSelfDualC W ΛW)
    (N : ℕ) (hN : 0 < N) :
    ∃ n : ℕ, ∀ k ∈ GfC V, GlobalTheory.Member.FinCong V n.factorial k →
      ∀ x ∈ (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True),
        ∃ l ∈ (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True),
          actO V W k 1 x = x + N • l := by
  by_contra hne
  push_neg at hne
  choose k hk hkc hkne using hne
  have ht := GlobalTheory.SplitCharTrivial.tendsto_one_of_finCong (k := k) hk hkc
  have ht2 : Filter.Tendsto (fun n => ((k n, (1 : GA D W)) : GA D V × GA D W)) Filter.atTop (𝓝 1) := by
    have := ht.prodMk_nhds (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (1 : GA D W)) Filter.atTop (𝓝 1))
    rwa [Prod.mk_one_one] at this
  obtain ⟨n, hn⟩ := (ht2.eventually (GlobalTheory.Mem.CoefInv.eventually_mod ΛV ΛW hV hW N hN)).exists
  obtain ⟨x, hx, hxne⟩ := hkne n
  obtain ⟨l, hl, e⟩ := hn x hx
  exact hxne l hl e

theorem psi_four_eq_one {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {Λ : AddSubgroup (WO S T)} {f : WO S T → ℂ}
    (hlat : ∀ u ∈ Λ, heisO ψ S T (2 • u) f = f) {w₀ : WO S T} (hw₀ : f w₀ ≠ 0) {a b : WO S T} (ha : a ∈ Λ)
    (hb : b ∈ Λ) : ψ (symplO S T ((2 * 2) • a) b) = 1 := by
  have h := GlobalTheory.SplitScalar.heisO_comm ψ S T (2 • a) (2 • b) f
  rw [hlat b hb, hlat a ha, hlat b hb] at h
  have h3 := congrFun h w₀
  rw [Pi.smul_apply, smul_eq_mul] at h3
  have h4 : ψ (symplO S T (2 • a) (2 • b)) = 1 :=
    mul_right_cancel₀ hw₀ (h3.symm.trans (one_mul _).symm)
  rwa [← GlobalTheory.Mem.CoefInv.symplO_nsmul, smul_smul] at h4

theorem lat_iff_of_mod {V W : HSp D} {L : AddSubgroup (WO V W)} {n : ℕ}
    (hn : ∀ k ∈ GfC V, GlobalTheory.Member.FinCong V n.factorial k → ∀ x ∈ L, ∃ l ∈ L, actO V W k 1 x = x + 1 • l)
    {k : GA D V} (hk : k ∈ GlobalTheory.Member.PrincLevel.levelGroup V n.factorial) :
    ∀ u : WO V W, u ∈ L ↔ ∃ u₀ ∈ L, u = actO V W k 1 u₀ := by
  have hki := inv_mem hk
  intro u
  constructor
  · intro hu
    obtain ⟨l, hl, e⟩ := hn k⁻¹ hki.1 hki.2 u hu
    refine ⟨actO V W k⁻¹ 1 u, by rw [e, one_nsmul]; exact L.add_mem hu hl, ?_⟩
    have := GlobalTheory.WeilVacMove.actO_inv_actO k⁻¹ (1 : GA D W) u
    rw [inv_inv, inv_one] at this
    exact this.symm
  · rintro ⟨u₀, hu₀, rfl⟩
    obtain ⟨l, hl, e⟩ := hn k hk.1 hk.2 u₀ hu₀
    rw [e, one_nsmul]
    exact L.add_mem hu₀ hl

end GlobalTheory.VacTranslate
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiToBesselNonvanishingTower
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.AscRungB

theorem rapidDec_star {D : D7} {V : HSp D} {f : GA D V → ℂ} (h : RapidDec V f) : RapidDec V (star f) := by
  first
  | exact h.conj
  | exact RapidDec.of_le h (fun γ hγ g => by simp only [Pi.star_apply]; rw [h.left hγ g])
      h.continuous.star (fun g => by simp only [Pi.star_apply, norm_star, le_refl])

theorem exists_step {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ)
    {χV χW : (AE D)ˣ →* Circle} {om : Om V W} (h : IsWeilDatumO ψ V W χV χW om) (vW : GlobalTheory.Unf.Vol W) :
    ∃ s : Step ψ V V₀ W W₀ ρ σ, s.χV = χV ∧ s.χW = χW ∧ s.om = om ∧ s.vW = vW := by
  have hDesc := GlobalTheory.Unf.descent_of_weilDatumExists D (GlobalTheory.WeilDatumExistence.weilDatumExists D)
  obtain ⟨om₁, h₁⟩ := (hDesc ψ V W χV χW om h).1 V₀ ρ dV
  obtain ⟨om₀, h₀⟩ := (hDesc ψ V₀ W χV χW om₁ h₁).2 W₀ σ dW
  obtain ⟨vS⟩ := GlobalTheory.Unf.VolExist.nonempty_volM D W.rank ρ
  obtain ⟨vT⟩ := GlobalTheory.Unf.VolExist.nonempty_volM D σ V₀.rank
  obtain ⟨vU⟩ := GlobalTheory.Unf.VolExist.nonempty_volU D ρ
  exact ⟨⟨χV, χW, om, om₀, h, h₀, vW, vS, vT, vU⟩, rfl, rfl, rfl, rfl⟩

theorem rungB : FockTot → PartFixed → RungB := by
  intro hF hP
  unfold RungB OnTower
  intro D hD T L μ0 hL sc G W M hM v F ΓL _hEnds hGood Ψ hΨ u hu k h hJ

  have hi : 2 * k + 1 < D.R.m := by omega
  obtain ⟨hw1, hw2, hodd, -, hdepiff, hdn, hpart, hpartEq, hhaar, hfund⟩ :=
    _root_.GlobalTheory.Asc.conjRead_holds D hD T L μ0 hL sc G W M hM (2 * k + 1) hi
  obtain ⟨hχS, hχT⟩ := hodd (odd_two_mul_add_one k)
  obtain ⟨hrap, hchain⟩ := hΨ
  obtain ⟨f, hdep, hΨeq⟩ := hchain (2 * k + 1) hi
  obtain ⟨χ', omz, hwz, ρ, Φ, Φ₀, hΦ₀, hne⟩ := hJ

  let vW : GlobalTheory.Unf.Vol (G.V (.grid (2 * k + 1) 0)) := ⟨M.ν _, M.fd _, hhaar, hfund⟩
  obtain ⟨s, hsV, hsW, hsom, hsvW⟩ := exists_step (F.dB k h) (F.dJ k h) hw1 vW
  obtain ⟨𝒮, Γ₀, hLoc, hvacS, hbox⟩ := hGood.bf k h s hsom

  set φ : GA D (G.V (.core (2 * k + 2))) → ℂ := star (Ψ (2 * k + 2))
  set G' : GA D (G.V (.grid (2 * k + 1) 0)) → ℂ := star (part W M ρ Φ u (2 * k + 1) (by omega))
  have hφ : RapidDec _ φ := rapidDec_star (hrap (2 * k + 2) h)
  have hG' : RapidDec _ G' := rapidDec_star (hu ρ Φ (2 * k + 1) (by omega))
  have hfix : ∀ k' ∈ lev G (.grid (2 * k + 1) 0), ∀ g, G' (g * k') = G' g := fun k' hk' g =>
    congrArg star (hP D hD T L μ0 hL sc G W M hM ρ Φ u (2 * k) (by omega) k' hk' g)

  have hvac1 : VacG W.ψ _ _ (latCore G (2 * k + 1)) (star f) := (hdepiff f).1 hdep
  obtain ⟨-, hlink⟩ := _root_.GlobalTheory.LinkInvTheta.link_inv_theta D W.ψ W.ψ_std (negSp F.Lz) (negSp F.Lz) (G.V (.core (2 * k + 1)))
    (F.ζ (k + 1)) (F.ζ k) (F.line (k + 1)) (F.line k) (F.lnk k)
  obtain ⟨Ξ₂, hΞ₂, hΦ₀eq⟩ := hlink Φ₀ hΦ₀.1
  have hbox' := hbox (star f) Ξ₂ hvac1 hΞ₂ (by rw [← hΦ₀eq]; exact hΦ₀)

  have hlift : liftT (omCore W (2 * k + 1)) (v (2 * k + 2)).μ (v (2 * k + 2)).𝓕 φ (star f) = star (Ψ (2 * k + 1)) := by
    rw [hΨeq]; exact (hdn v f (Ψ (2 * k + 2))).symm
  have hJper : (F.jac v k h).per W.ψ (F.ζ k) omz
      (liftT (omCore W (2 * k + 1)) (v (2 * k + 2)).μ (v (2 * k + 2)).𝓕 φ (star f)) G'
      (fun w => star (Ξ₂ ((F.lnk k).κ _ w))) ≠ 0 := by
    rw [hlift, ← hΦ₀eq]; exact hne
  have hsχ : s.χV = (G.ch.chi (D.R.m - (2 * k + 1)))⁻¹ * L.eta := by rw [hsV, hχS]
  have hWA : IsWeilDatumO W.ψ _ _ (G.ch.chi (D.R.m - (2 * k + 1)))⁻¹ s.χW (omCore W (2 * k + 1)) := by
    rw [hsW, hχT]; exact hw2
  obtain ⟨Φ₁, hΦ₁S, hper₁⟩ := _root_.GlobalTheory.UpBessel.upBF D W.ψ k (F.bes v k h) (F.jac v k h) s 𝒮 Γ₀ _ hLoc (negSp F.Lz) (F.ζ k)
    (F.line k) (F.lnk k) _ _ χ' (omCore W (2 * k + 1)) omz hsχ hWA hwz φ G' hφ hG' hfix (star f) Ξ₂ hvac1.1 hΞ₂ hbox' hJper

  set ℓ : (WO (G.V (.grid (2 * k + 2) 0)) (G.V (.grid (2 * k + 1) 0)) → ℂ) → ℂ :=
    fun Φ' => (F.bes v k h).per W.ψ φ (liftS (omRow W (2 * k + 1)) vW.μ vW.𝓕 G' Φ')
  have htame : Tame W.ψ _ _ ℓ :=
    (_root_.GlobalTheory.LiftTame.lift_periods_tame D W.ψ _ vW G' hG').1 k (F.bes v k h) _ _ (omRow W (2 * k + 1)) hw1 φ hφ
  have hℓ₁ : ℓ Φ₁ ≠ 0 := by
    have e : s.lift G' Φ₁ = liftS (omRow W (2 * k + 1)) vW.μ vW.𝓕 G' Φ₁ := by
      unfold GlobalTheory.Unf.Step.lift; rw [hsom, hsvW]
    rw [e] at hper₁; exact hper₁

  by_contra hall
  apply hℓ₁
  refine hF D hD T L μ0 hL sc G W M hM ⟨2 * k + 1, hi⟩ ℓ htame ?_ Φ₁ (hvacS Φ₁ hΦ₁S)
  intro κ P
  let ρ' : G.RealVec := Function.update ρ ⟨2 * k + 1, hi⟩ P
  let Φ' : G.Datum := Function.update Φ ⟨2 * k + 1, hi⟩ κ
  have hagree : ∀ j : Fin D.R.m, j.1 < 2 * k + 1 → ρ' j = ρ j ∧ Φ' j = Φ j := by
    intro j hj
    have hne' : j ≠ ⟨2 * k + 1, hi⟩ := fun e => by rw [e] at hj; exact lt_irrefl _ hj
    exact ⟨Function.update_of_ne hne' _ _, Function.update_of_ne hne' _ _⟩
  have hdat : W.datum ρ' Φ' ⟨2 * k + 1, hi⟩ = W.fock (.chi (2 * k + 1) 0) (W.cosVec (2 * k + 1) κ) P := by
    simp only [GlobalTheory.ChiGrid.GridData.Weil.datum, ρ', Φ', Function.update_self]
  have htop := hpart ρ' Φ' u
  rw [hpartEq ρ' Φ' ρ Φ u hagree, hdat] at htop
  have h0 : (F.bes v k h).per W.ψ φ (star (part W M ρ' Φ' u (2 * k + 1 + 1) hi)) = 0 := by
    by_contra hne0
    exact hall ⟨ρ', Φ', hne0⟩
  rw [htop] at h0
  exact h0

end GlobalTheory.AscRungB

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeKernelComplexPointMatchesCosets
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.HeckeTermIdent

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GeoTie
open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits
open ReciprocityTheory.ChartRestriction.G GlobalTheory.IndefiniteRowSideFullHecke.HeckeIsogenyKernels GlobalTheory.HeckeCompare GlobalTheory.HeckeCount

theorem nonempty_hkKer_equiv {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l)
    (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (P : Ideal (𝓞 E)) (q i : ℕ) (hP : GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.IsHeckePrime l P q)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (z : FrPt Xo c Ω) :
    Nonempty (hkKer (Xo := Xo) P q i Ω z ≃ LatCount Dw q (conjIdeal H P) (Ideal.absNorm P ^ i)) := by
  have hs : IsSplitPrimeOff l q P := (splitPrime_iff l q P).2 (GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.isHeckePrime_iff.1 hP)
  have : CharZero Ω := charZero_of_injective_ringHom (Spec.preimage (z.x ≫ Xo.s)).hom.injective
  obtain ⟨o, ⟨m⟩⟩ := exists_fibre_obj Xo z.x z.x rfl
  obtain ⟨eT⟩ := nonempty_transfer_equiv Xo.univ m P q i
  obtain ⟨eL⟩ := nonempty_datum_equiv GlobalTheory.firstFiveLaws.1 o hs i
  exact ⟨eT.symm.trans ((heckeKerEquivDatum GlobalTheory.firstFiveLaws.1 o hs i).trans eL)⟩

end GlobalTheory.HeckeTermIdent

namespace GlobalTheory.HeckeTermIdent

open NumberField

theorem isHeckePrime_of_setting {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type}
    {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F}
    {i : Fin D.R.m} {P : Formalism.L2.DIV.Pl D.host.E} {p k : ℕ} {α : GA D (Wc D i)} {Rc : Finset (GA D (Wc D i))}
    (hS : GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsUnitaryHeckeOperatorSplitPrimeData T R i P p k α Rc) :
    GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.IsHeckePrime T.Q.l P.asIdeal p := by
  obtain ⟨hOff, hp, hpP, hM, -⟩ := hS
  refine GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.isHeckePrime_iff.2 ⟨P.isMaximal, ?_, hp, hpP, hM⟩
  let b : 𝓞 D.host.E ≃+* 𝓞 D.host.E := Formalism.L2.Pj.barE D
  have hb : ∀ a : 𝓞 D.host.E, T.Q.H.bar a = b a := fun a => GlobalTheory.IndefiniteRowSideFullHecke.HalfDepthValuations.bar_eq_barE T.Q a
  have hmap : P.asIdeal.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = P.asIdeal.map (b : 𝓞 D.host.E →+* 𝓞 D.host.E) := by
    congr 1; exact RingHom.ext hb
  have hconj : Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal = P.asIdeal.map (b : 𝓞 D.host.E →+* 𝓞 D.host.E) := by
    apply le_antisymm
    · rw [Formalism.HermitianLatticesTheory.conjIdeal, Ideal.span_le]
      rintro r ⟨s, hs, e⟩
      have : r = b s := by
        apply RingOfIntegers.coe_injective
        exact e.trans rfl
      rw [this]
      exact Ideal.mem_map_of_mem _ hs
    · rw [Ideal.map_le_iff_le_comap]
      intro s hs
      exact Ideal.subset_span ⟨s, hs, rfl⟩
  have hmax : (P.asIdeal.map (b : 𝓞 D.host.E →+* 𝓞 D.host.E)).IsMaximal := Ideal.map_isMaximal_of_equiv b
  have hne : P.asIdeal ≠ P.asIdeal.map (b : 𝓞 D.host.E →+* 𝓞 D.host.E) := by
    intro e; exact hOff.1 (hconj.trans e.symm)
  rw [hmap]
  exact P.isMaximal.coprime_of_ne hmax hne

end GlobalTheory.HeckeTermIdent

namespace GlobalTheory.HeckeTermIdent

open NumberField

theorem heckeKernelCoset : ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.HeckePointLaws → GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.SplitLinearModel D → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.VacFixed D →
    ∀ (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), σ = T.σ₀ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i,
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i σ hV →
    ∀ (P : Formalism.L2.DIV.Pl D.host.E) (p k : ℕ) (α : GA D (Wc D i)) (Rc : Finset (GA D (Wc D i))),
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsUnitaryHeckeOperatorSplitPrimeData T R i P p k α Rc →
    ∀ (h : GA D (Wc D i))
      (hx : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1).dom),
      letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
      haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
      ∃ e : hkKer (Xo := T.Q.Xo ((i : ℕ) + 1)) P.asIdeal p k (CAt σ) ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩) ≃ Rc,
        ∀ C z, hkRelFr P.asIdeal p k (GlobalTheory.ThetaTrace.hkTr (T.Q.Xo ((i : ℕ) + 1)) T.Q.c p) (CAt σ) ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩) C z →
          ∃ (hx' : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * (e C : GA D (Wc D i)))).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * (e C : GA D (Wc D i)))).1).dom) (t : Ix (T.Q.Dw ((i : ℕ) + 1)) → (CAt σ)ˣ),
            (∀ j, j ≠ none → t j = 1) ∧ FrBor t ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * (e C : GA D (Wc D i)))).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * (e C : GA D (Wc D i)))).2, hx'⟩) z := by
  intro D hHk hSL hVF G _ _ Pl0 T0 A T _ R F κ v₀ hLev hGrp hFam hMod hThP hTie i σ hσ hV hFP P p k α Rc hS h hx
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
  have hP := GlobalTheory.HeckeTermIdent.isHeckePrime_of_setting hS
  have hE := GlobalTheory.T.exists_heckeKernel_coset_framedPoint D hHk hSL hVF G Pl0 T0 A T R F κ v₀ hLev hGrp hFam hMod hThP hTie i σ hσ hV hFP P p k α Rc hS h hx
  choose f hfR hfZ using hE
  have hTot := hHk.2.1 _ _ _ _ (T.Q.Xo ((i : ℕ) + 1)) T.Q.c P.asIdeal p k hP (CAt σ) ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩)
  have hU : IsUnf (T.U ((i : ℕ) + 1) σ) := hTie.laws.unf _ ⟨Nat.le_add_left _ _, i.2⟩ σ (hσ ▸ T.toCore.good_σ₀)
  let g : hkKer (Xo := T.Q.Xo ((i : ℕ) + 1)) P.asIdeal p k (CAt σ) ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩) → Rc := fun C => ⟨f C, hfR C⟩
  have hinj : Function.Injective g := by
    intro C C' hCC
    have e : f C = f C' := congrArg Subtype.val hCC
    obtain ⟨z, hz⟩ := hTot C
    obtain ⟨z', hz'⟩ := hTot C'
    obtain ⟨hx1, t, ht, hb⟩ := hfZ C z hz
    have key : ∀ a, f C' = a → ∃ (hx' : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).2 ∈
        ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).1).dom) (t : Ix (T.Q.Dw ((i : ℕ) + 1)) → (CAt σ)ˣ),
        (∀ j, j ≠ none → t j = 1) ∧ FrBor t ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).2, hx'⟩) z' := by
      rintro a rfl; exact hfZ C' z' hz'
    obtain ⟨hx2, t', ht', hb'⟩ := key (f C) e.symm
    exact GlobalTheory.T.heckeKernel_eq_of_unipotent_frameChange (T.Q.Xo ((i : ℕ) + 1)) T.Q.c σ D.R.r (T.U ((i : ℕ) + 1) σ) hU P.asIdeal p k hP _ _ C C' z z' _ t t'
      hz hz' ht ht' hb hb'
  have hfin : Finite (hkKer (Xo := T.Q.Xo ((i : ℕ) + 1)) P.asIdeal p k (CAt σ) ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩)) := Finite.of_injective g hinj
  obtain ⟨eK⟩ := GlobalTheory.HeckeTermIdent.nonempty_hkKer_equiv (T.Q.Xo ((i : ℕ) + 1)) T.Q.c P.asIdeal p k hP (CAt σ) ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩)
  have hcard : Nat.card Rc ≤ Nat.card (hkKer (Xo := T.Q.Xo ((i : ℕ) + 1)) P.asIdeal p k (CAt σ) ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩)) := by
    rw [Nat.card_congr eK, ← _root_.GlobalTheory.HeckeCosetCount.card_eq_latCount D hHk hSL hVF G Pl0 T0 A T R F κ v₀ hLev hGrp hFam hMod hThP hTie i σ hσ hV hFP P p k α Rc hS,
      Nat.card_eq_fintype_card, Fintype.card_coe]
  refine ⟨Equiv.ofBijective g (hinj.bijective_of_nat_card_le hcard), fun C z hz => hfZ C z hz⟩

end GlobalTheory.HeckeTermIdent
end
end

