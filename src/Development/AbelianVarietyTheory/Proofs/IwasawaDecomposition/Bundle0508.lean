module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0497
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalBoundaryMetricData
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0020
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.ExistsBasicOpenCover
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartWiden
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValLtOfRedM
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0434
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0443
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnKernelDataCompatibleStepCharts
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0450
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0439
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0454
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0459
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0280
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0031
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Formalism.LocalRingCardinality.SpanPowerMembership.HaarDensityNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0268
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0308
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0350
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0465
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0495
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0278
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MovedFiniteDatumFourierExpansionChainless
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PureTensorOSmul
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0429

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FourierJacobiConstantTermEqZeroOfFlowLine
section
open NumberField Complex ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CuspFrom Filter Topology

namespace GlobalTheory.CuspLimit


open Classical in
theorem tendsto_dirichlet {ι : Type*} (A : ι → ℂ) (a : ι → ℝ) (F : ℝ → ℂ) (T : ℝ)
    (ha : ∀ i, A i ≠ 0 → 0 ≤ a i)
    (hs : ∀ t, T < t → HasSum (fun i => A i * (Real.exp (-(a i * t)) : ℂ)) (F t)) :
    Tendsto F atTop (𝓝 (∑' i, if a i = 0 then A i else 0)) := by
  have h0 : Summable fun i => ‖A i * (Real.exp (-(a i * (T + 1))) : ℂ)‖ :=
    (hs (T + 1) (by linarith)).summable.norm
  have hlim : Tendsto (fun t : ℝ => ∑' i, A i * (Real.exp (-(a i * t)) : ℂ)) atTop
      (𝓝 (∑' i, if a i = 0 then A i else 0)) := by
    refine tendsto_tsum_of_dominated_convergence h0 (fun i => ?_) ?_
    · by_cases hi : A i = 0
      · simp [hi]
      by_cases hz : a i = 0
      · simp [hz]
      have hp : 0 < a i := lt_of_le_of_ne (ha i hi) (Ne.symm hz)
      rw [if_neg hz]
      have h1 : Tendsto (fun t : ℝ => Real.exp (-(a i * t))) atTop (𝓝 0) :=
        Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hp)
      have h2 := ((Complex.continuous_ofReal.tendsto 0).comp h1).const_mul (A i)
      simpa using h2
    · filter_upwards [eventually_ge_atTop (T + 1)] with t ht i
      by_cases hi : A i = 0
      · simp [hi]
      rw [norm_mul, norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le,
        Complex.norm_of_nonneg (Real.exp_pos _).le]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
      exact neg_le_neg (mul_le_mul_of_nonneg_left ht (ha i hi))
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop T] with t ht
  exact (hs t ht).tsum_eq

theorem fj_zero_eq_zero_of_line : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (ξ : Fin r → E) (x : Frame X.Ψ r) (s : X.Ψ → ℂ) (d : X.Ψ → ℝ) (T : ℝ) (g : ℤ → ℂ), X.IsSec la P → FreqNonneg X la P → X.IsIso ξ → x ∈ X.dom → (∀ τ, 0 < d τ) → (∀ m ≤ 0, g m = 0) → (∀ w : ℂ, T < w.im → X.flow ξ (fun τ => s τ + w * (d τ : ℂ)) x ∈ X.dom ∧ HasSum (fun m : ℤ => g m * ReciprocityTheory.ChartRestriction.G.Geo.Tor.eTwoPi w ^ m) (P (X.flow ξ (fun τ => s τ + w * (d τ : ℂ)) x))) → X.fj la ξ 0 P x = 0 := by
  intro E _ _ _ r X la P ξ x s d T g hP hnn hξ hx hd hg hw
  classical
  have hpi := Real.pi_pos
  set F : ℝ → ℂ := fun t => P (X.flow ξ (fun τ => s τ + (I * t) * (d τ : ℂ)) x) with hF
  have him : ∀ t : ℝ, T < t → T < (I * (t : ℂ)).im := fun t ht => by simpa using ht
  have h1 := tendsto_dirichlet g (fun m : ℤ => 2 * Real.pi * m) F T
    (fun m hm => by
      have : 0 < m := by
        by_contra h
        exact hm (hg m (not_lt.mp h))
      positivity)
    (fun t ht => by
      have h := (hw _ (him t ht)).2
      convert h using 3 with m
      rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.eTwoPi, ← Complex.exp_int_mul]
      push_cast
      congr 1
      linear_combination (-(2 * (Real.pi : ℂ) * m * t)) * Complex.I_mul_I)
  have e1 : (∑' m : ℤ, if 2 * Real.pi * (m : ℝ) = 0 then g m else 0) = 0 := by
    have : (fun m : ℤ => if 2 * Real.pi * (m : ℝ) = 0 then g m else 0) = fun _ => 0 := by
      funext m
      split_ifs with h
      · have hm : m = 0 := by simpa [hpi.ne'] using h
        exact hg m hm.le
      · rfl
    rw [this, tsum_zero]
  have h2 := tendsto_dirichlet
    (fun ν : X.Ψ → ℝ => X.fj la ξ ν P x * cexp (4 * Real.pi * I * ∑ τ, (ν τ : ℂ) * s τ))
    (fun ν => 4 * Real.pi * ∑ τ, ν τ * d τ) F T
    (fun ν hν => by
      have h0 := hnn ξ hξ ν x hx (left_ne_zero_of_mul hν)
      have : 0 ≤ ∑ τ, ν τ * d τ := Finset.sum_nonneg fun τ _ => mul_nonneg (h0 τ) (hd τ).le
      positivity)
    (fun t ht => by
      have h := m3bExp_holds r X la P hP ξ hξ x hx _ (hw _ (him t ht)).1
      convert h using 2 with ν
      rw [mul_assoc]
      congr 1
      push_cast
      rw [← Complex.exp_add]
      congr 1
      have e : ∑ τ, (ν τ : ℂ) * (s τ + I * t * (d τ : ℂ)) =
          ∑ τ, (ν τ : ℂ) * s τ + I * t * ∑ τ, (ν τ : ℂ) * (d τ : ℂ) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun τ _ => by ring
      rw [e]
      linear_combination (-(4 * (Real.pi : ℂ) * t * ∑ τ, (ν τ : ℂ) * (d τ : ℂ))) * Complex.I_mul_I)
  rw [tsum_eq_single (0 : X.Ψ → ℝ) (fun ν hν => by
    split_ifs with h
    · by_contra hne
      have h0 := hnn ξ hξ ν x hx (left_ne_zero_of_mul hne)
      have hz : ∑ τ, ν τ * d τ = 0 := by simpa [hpi.ne'] using h
      refine hν (funext fun τ => ?_)
      have := (Finset.sum_eq_zero_iff_of_nonneg fun τ _ => mul_nonneg (h0 τ) (hd τ).le).mp hz τ
        (Finset.mem_univ τ)
      exact (mul_eq_zero.mp this).resolve_right (hd τ).ne'
    · rfl)] at h2
  rw [e1] at h1
  simpa using tendsto_nhds_unique h2 h1

end GlobalTheory.CuspLimit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromSpecStalkMemZeroLocusIff
section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

namespace GlobalTheory.SncComponents

theorem fromSpecStalk_mem_zeroLocus_iff {Y : Scheme.{0}} (U : Y.affineOpens) (x : Y) (hx : x ∈ U.1)
    (f : Γ(Y, U.1)) (q : PrimeSpectrum (Y.presheaf.stalk x)) :
    Y.fromSpecStalk x q ∈ Y.zeroLocus {f} ↔ Y.presheaf.germ U.1 x hx f ∈ q.asIdeal := by
  have hU : IsAffineOpen U.1 := U.2
  have e : Y.fromSpecStalk x q =
      hU.fromSpec (PrimeSpectrum.comap (Y.presheaf.germ U.1 x hx).hom q) := by
    rw [← hU.fromSpecStalk_eq_fromSpecStalk hx]
    rfl
  rw [Scheme.mem_zeroLocus_iff, e]
  simp only [Set.mem_singleton_iff, forall_eq]
  have h := hU.fromSpec_preimage_basicOpen f
  have h2 : hU.fromSpec (PrimeSpectrum.comap (Y.presheaf.germ U.1 x hx).hom q) ∈ Y.basicOpen f ↔
      PrimeSpectrum.comap (Y.presheaf.germ U.1 x hx).hom q ∈ PrimeSpectrum.basicOpen f :=
    iff_of_eq (congrArg (fun V => PrimeSpectrum.comap (Y.presheaf.germ U.1 x hx).hom q ∈ V) h)
  exact (not_congr h2).trans not_not

theorem effCartier_of_mem_comps {Y : Scheme.{0}} [IsNoetherian Y] {Z : Y.IdealSheafData}
    (hZ : FinalTheorems.Snc Z) (C : Closeds Y) (hC : (C : Set Y) ∈ comps (Z.support : Set Y)) :
    FinalTheorems.EffCartier (Scheme.IdealSheafData.vanishingIdeal C) := by
  refine effCartier_of_stalkId _ fun x => ?_
  obtain ⟨hreg, U, hx, n, f, J, hrsp, hZU⟩ := hZ x
  obtain ⟨O, hxO, -, hO⟩ := exists_open_comps x U hx f J hrsp hZU
  have hO' := hO _ hC
  have hq : ∀ q : PrimeSpectrum (Y.presheaf.stalk x), Y.fromSpecStalk x q ∈ (C : Set Y) ↔
      ∃ i ∈ J, IsBranch (Z.support : Set Y) (f i) x C ∧
        Y.presheaf.germ U.1 x hx (f i) ∈ q.asIdeal := by
    intro q
    have hqO : Y.fromSpecStalk x q ∈ (O : Set Y) := by
      have h : Y.fromSpecStalk x q ∈ Set.range (Y.fromSpecStalk x) := ⟨q, rfl⟩
      rw [Scheme.range_fromSpecStalk] at h
      exact Specializes.mem_open h O.isOpen hxO
    have h := Set.ext_iff.1 hO' (Y.fromSpecStalk x q)
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, hqO, and_true, true_and,
      fromSpecStalk_mem_zeroLocus_iff U x hx] at h
    exact h
  have hCC : C.compl.compl = C := SetLike.coe_injective (compl_compl _)
  by_cases hb : ∃ i ∈ J, IsBranch (Z.support : Set Y) (f i) x C
  · obtain ⟨i, hi, hbi⟩ := hb
    have hp : Prime (Y.presheaf.germ U.1 x hx (f i)) :=
      prime_of_regular_params (fun i => Y.presheaf.germ U.1 x hx (f i)) hrsp.1 hrsp.2 i
    haveI : IsDomain (Y.presheaf.stalk x) := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.isDomain _
    refine ⟨_, mem_nonZeroDivisors_of_ne_zero hp.ne_zero, ?_⟩
    have h := AffineComplement.stalkId_vanishingIdeal_compl C.compl x
      (Y.presheaf.germ U.1 x hx (f i)) fun q => by
        refine not_congr ((hq q).trans ⟨?_, fun h => ⟨i, hi, hbi, h⟩⟩)
        rintro ⟨j, hj, hbj, h⟩
        by_cases hij : i = j
        · exact hij ▸ h
        · exact absurd rfl (branch_ne x U hx f J hrsp hZU hi hj hij hbi hbj)
    rw [hCC] at h
    rw [h]
    exact ((Ideal.span_singleton_prime hp.ne_zero).2 hp).radical
  · refine ⟨1, one_mem _, ?_⟩
    have h := AffineComplement.stalkId_vanishingIdeal_compl C.compl x 1 fun q => by
      refine not_congr ((hq q).trans ⟨?_, fun h => ?_⟩)
      · rintro ⟨j, hj, hbj, -⟩
        exact absurd ⟨j, hj, hbj⟩ hb
      · exact absurd ((Ideal.eq_top_iff_one _).2 h) q.isPrime.ne_top
    rw [hCC] at h
    rw [h, Ideal.span_singleton_one, Ideal.radical_top]

theorem exists_compList_effCartier (k : Type) [Field k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (d : ℕ)
    [SmoothOfRelativeDimension d p] [QuasiCompact p] (B : Closeds Y)
    (hB : FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal B)) :
    ∃ (m : ℕ) (C : Fin m → Closeds Y), FinalTheorems.CompList (B : Set Y) C ∧
      ∀ i, FinalTheorems.EffCartier (Scheme.IdealSheafData.vanishingIdeal (C i)) := by
  haveI : Smooth p := SmoothOfRelativeDimension.smooth d p
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian p
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace p
  haveI : IsNoetherian Y := {}
  haveI : Finite (comps (B : Set Y)) := (comps_finite _).to_subtype
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin (comps (B : Set Y))
  refine ⟨m, fun i => ⟨(e.symm i).1, isClosed_of_mem_comps B.isClosed (e.symm i).2⟩,
    ⟨fun i => (e.symm i).2.1.1, ?_, fun i j hij => ?_⟩, fun i => ?_⟩
  · conv_rhs => rw [← sUnion_comps (B : Set Y), Set.sUnion_eq_iUnion]
    exact e.symm.surjective.iUnion_comp (fun c => (c.1 : Set Y))
  · have hi : Maximal (fun C => IsIrreducible C ∧ C ⊆ (B : Set Y)) (e.symm i).1 := (e.symm i).2
    exact e.symm.injective (Subtype.ext (Set.Subset.antisymm hij (hi.2 (e.symm j).2.1 hij)))
  · refine effCartier_of_mem_comps hB _ ?_
    have hs : ((Scheme.IdealSheafData.vanishingIdeal B).support : Set Y) = B := by simp
    rw [hs]
    exact (e.symm i).2

end GlobalTheory.SncComponents
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FurtherPlacePenultimateChartCharacterInverseValu
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.QChi.LocVal

theorem midLev_one_one {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (a : I.ι) (i : ℕ) (hi : i < B.R.m) (al : (I.idx a).β i)
    (P : SBof I a) : GlobalTheory.TwU.MidLev (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) i P ((I.idx a).h i al P) 1 1 := by
  classical
  obtain ⟨z, r, hr, hrx, hz⟩ := (GlobalTheory.TwU.exists_midLev_iff I.Ch I.sel (I.tup a) (I.cst a) i P ((I.idx a).h i al P) 1).2 (Subgroup.one_mem _)
  refine ⟨r, hr, hrx, ?_⟩
  by_cases hP : P.1 ∈ (B.primes X).vGs
  · rw [chiInv_at_type I hOk a i al P hP 1 1 r hr hrx 1 (one_mem _) (fun x _ => by simp) (congE_refl _ _ _)]
    have e : (((I.idx a).levG i al) ⟨P.1, hP⟩).lam ⟨1, one_mem _⟩ = 1 := map_one (((I.idx a).levG i al) ⟨P.1, hP⟩).lam
    rw [e]; simp
  · have hQ : P.1 ∈ I.Q a := (Finset.mem_union.mp P.2).resolve_left hP
    rw [chiInv_at_twist I hOk a i hi al P hQ 1 1 r hr hrx 1 (one_mem _) (by simp) (congE_refl _ _ _)]
    have e : (((I.idx a).levQ i al) ⟨P.1, hQ⟩).lam ⟨1, one_mem _⟩ = 1 := map_one (((I.idx a).levQ i al) ⟨P.1, hQ⟩).lam
    rw [e]; simp


open Classical in
theorem exists_frNear_one_over {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) (n : ℕ)
    (k : GL (Fin n) (AfE (I.rec7 l Z).host.F (I.rec7 l Z).host.E)) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))
    (hk : bc (prV (E := (I.rec7 l Z).host.E) v) k = 1) :
    ∃ fb : SBof I a → GL (Fin n) (I.rec7 l Z).host.E, FrNear I l Z a k fb ∧ ∀ P, IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) → fb P = 1 := by
  obtain ⟨fb0, h0⟩ := GlobalTheory.Mem.Col2.AdT.frNear_exists I hOk l Z a n k
  refine ⟨fun P => if IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) then 1 else fb0 P, fun P => ?_, fun P hP => if_pos hP⟩
  by_cases hv : IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1)
  · simp only [if_pos hv]
    refine ⟨?_, ?_⟩
    · have h2 := GlobalTheory.AwayFr.congAt_of_prV_eq _ _ hv ((I.cst a).D P) k 1 (by rw [map_one, hk])
      simpa using h2
    · have h2 := GlobalTheory.AwayFr.congAt_of_prV_eq _ _ hv ((I.cst a).D P) 1 k (by rw [map_one, hk])
      simpa using h2
  · simp only [if_neg hv]
    exact h0 P

theorem nearAt_emb_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E)) (hP : ¬ IsOver v P) (d : ℕ)
    (x : GL (Fin n) (E ⊗[F] v.adicCompletion F)) (y : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (g : GL (Fin n) E) (hg : g = 1) :
    GlobalTheory.TwU.NearAt P d (y⁻¹ * GlobalTheory.Mem.Col2.ChartLevel.emb v x * y) g := by
  subst hg
  have hw : IsOver (P.under (𝓞 F)) P := by
    unfold IsOver
    rw [HeightOneSpectrum.under_asIdeal]
  have hne : P.under (𝓞 F) ≠ v := fun e => hP (e ▸ hw)
  unfold GlobalTheory.TwU.NearAt
  refine GlobalTheory.AwayFr.congAt_of_prV_eq _ _ hw d _ _ ?_
  rw [map_one, map_one, map_mul, map_mul, GlobalTheory.Mem.Col2.ChartLevel.emb_ne hne, mul_one, ← map_mul, inv_mul_cancel, map_one]

end GlobalTheory.Mem.Col2.QChi.LocVal

namespace GlobalTheory.Mem.Col2.QChi


set_option maxHeartbeats 4000000 in
theorem chi_embU_mul_valV : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Ch0 : B.Word → ℕ → Type) (chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (h1 : 1 ≤ B.R.m - 1) (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) (g : Ch → Ch0 u (B.R.m - 1)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u)) → (∀ u j v h, (F u).glevJ.fr j v h = 1) → (∃ k : Ch → GA B (B.R.N (B.R.m - 1)), I.Reads u a (B.R.m - 1) chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧ ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1) → (∀ β, GlobalTheory.Mem.Col2.AdT.ChiFin I l Z (K β).lev) → (∀ β, ∀ v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) → (∀ β (κ : (K β).lev.U) (κ' : ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.chi κ') → ∀ (Lb0 : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin ((I.rec7 l Z).sp.X (B.R.m - 1)).rank → (I.rec7 l Z).host.E)), (F u).levJ.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) Lb0 → ∀ (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), v ∈ Q → ∀ β (x : (K β).lev.Uloc v), (((K β).lev.chi (GlobalTheory.Mem.Col2.ChartLevel.embU (K β).lev v x) : ℂˣ) : ℂ) * GlobalTheory.Mem.Col2.QChi.valV I l Z a v x.1 = 1 := by
  intro B X I hOk hPins l Z Ch0 chOf0 F u a Q h1 Ch _ chOf K g hQ _ _ hRd hFin _ _ Lb0 _ v hvQ β x
  classical
  obtain ⟨k, hR, hk1⟩ := hRd
  obtain ⟨c, rfl⟩ := hR.onto β
  obtain ⟨fb, hfb, hfb1⟩ := LocVal.exists_frNear_one_over I hOk l Z a _ (k (chOf c)) v (hk1 _ v ((hQ v).1 hvQ))
  have hm : B.R.m - 1 < B.R.m := by omega
  have hlast : B.R.m - 1 + 1 = B.R.m := by omega
  let y0 : SBof I a → Sp B.fields.E (B.R.N (B.R.m - 1)) := fun P =>
    ((_root_.GlobalTheory.Mem.Col2.AdT.CosShape.cosShape I hOk u a _ ((I.stp u a _).rep c) P).2 hlast).1.some
  have H := lev_mid hOk hPins hR c hfb (hFin _) hm y0
    (Rel := fun P g z => MidAt I hm c.1 P g z ∧ (B.R.m - 1 + 1 = B.R.m → GlobalTheory.TwU.SameCoset I.sel (I.tup a) (I.cst a) P (g (y0 P)) (y0 P)))
    (fun _ P => ((_root_.GlobalTheory.Mem.Col2.AdT.CosShape.cosShape I hOk u a _ ((I.stp u a _).rep c) P).2 hlast).1.some_mem) (fun _ _ _ => Iff.rfl)
  have hx : bc (prV (E := (I.rec7 l Z).host.E) v) (GlobalTheory.Mem.Col2.ChartLevel.emb v x.1) ∈ (K (chOf c)).lev.Uloc v := by
    rw [GlobalTheory.Mem.Col2.ChartLevel.emb_self]; exact x.2
  have key : ∀ (P : SBof I a) (j : ℕ), j = B.R.m - 2 + 1 → ∀ b, (I.idx a).h j b P = 1 := by
    rintro P j rfl b
    exact (hOk.idx_ok a).last_h b P
  have hall : ∀ P : SBof I a, ∃ g z, ((MidAt I hm c.1 P g z ∧ (B.R.m - 1 + 1 = B.R.m →
      GlobalTheory.TwU.SameCoset I.sel (I.tup a) (I.cst a) P (g (y0 P)) (y0 P))) ∧
      GlobalTheory.TwU.InFrame (sm I l Z) fb (I.cst a).D P (GlobalTheory.Mem.Col2.ChartLevel.emb v x.1) g) ∧
      z = (if h : IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) ∧ ∃ g z, NearPair I l Z a v P x.1 g z then h.2.choose_spec.choose else 1) := by
    intro P
    by_cases hP : IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1)
    · obtain ⟨g, z, hrel, hin⟩ := H.1 P v hP _ (((K (chOf c)).lev.U_eq _).1 (GlobalTheory.Mem.Col2.ChartLevel.embU _ v x).2).1 hx
      have hnp : NearPair I l Z a v P x.1 g z := by
        refine ⟨?_, ?_⟩
        · have hmid := hrel.1
          unfold MidAt at hmid
          rw [key P _ (by omega)] at hmid
          exact hmid
        · have hin' := hin
          unfold NearV
          unfold GlobalTheory.TwU.InFrame at hin'
          rw [hfb1 P hP] at hin'
          first
            | (simp only [GlobalTheory.TwU.ratA, map_one, inv_one, one_mul, mul_one] at hin'; exact hin')
            | (erw [map_one, inv_one, one_mul, mul_one] at hin'; exact hin')
            | (convert hin' using 2; simp)
      have hh : IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) ∧ ∃ g z, NearPair I l Z a v P x.1 g z := ⟨hP, g, z, hnp⟩
      refine ⟨g, z, ⟨hrel, hin⟩, ?_⟩
      rw [dite_eq_left hh]
      exact nearPair_val_unique I hOk l Z a v P x.1 _ _ _ _ hnp hh.2.choose_spec.choose_spec
    · refine ⟨1, 1, ⟨⟨LocVal.midLev_one_one I hOk a _ hm _ P, fun _ t => ?_⟩, ?_⟩, by rw [dite_eq_right (fun h => hP (And.left h))]⟩
      · have e : ((1 : Sp B.fields.E (B.R.N (B.R.m - 1)) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N (B.R.m - 1))) (y0 P) - y0 P) t = 0 := by
          show (y0 P - y0 P) t = 0
          rw [sub_self]; rfl
        rw [e, mul_zero]
        simpa using GlobalTheory.TopInv.intAt_nat (P := P.1) 0
      · unfold GlobalTheory.TwU.InFrame
        exact LocVal.nearAt_emb_one v _ hP _ _ _ _ (map_one (GlobalTheory.TwU.seamGL (sm I l Z)))
  choose gg zz hgz hz using hall
  have hc := H.2.2 (GlobalTheory.Mem.Col2.ChartLevel.embU _ v x) gg zz hgz
  unfold valV
  rw [← Finset.prod_congr rfl fun P _ => hz P]
  exact hc

end GlobalTheory.Mem.Col2.QChi

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasBareOfHasPk
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw.Bare


set_option maxHeartbeats 2000000 in
theorem rows_le {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {y : Hd R.toRealDat}
    {mA : Bool → D.what₂.Tup → Mat1 D.what₂.LL G} {p : PkD D G} (t : PkT F y mA p) : (p.ch true).n ≤ p.Dall := by
  rcases Nat.eq_zero_or_pos p.Dall with h0 | hpos
  · have h := p.D_eq
    rw [h0, Nat.cast_zero, mul_zero] at h
    have h' : (p.ch true).n = 0 := by exact_mod_cast h
    omega
  · rw [t.dall] at hpos ⊢
    have hF := Module.finite_of_finrank_pos hpos
    have h1 := LinearMap.finrank_range_of_inj (t.ch true).jE_inj
    have h2 := Module.finrank_eq_card_basis (p.ch true).bs.toBasis
    rw [Fintype.card_fin] at h2
    rw [← h2, ← h1, (t.ch true).jE_range]
    have hle := Mult.goodPart_le R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 true)))
        (levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 true))) R.e0
    have hf := Submodule.finiteDimensional_of_le hle
    refine le_trans ?_ (Submodule.finrank_mono hle)
    exact Submodule.finrank_map_le (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _).toLinearMap
      (Mult.goodPart R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 true)))
        (levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 true))) R.e0)


set_option maxHeartbeats 2000000 in
theorem frames_unit {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {y : Hd R.toRealDat}
    {mA : Bool → D.what₂.Tup → Mat1 D.what₂.LL G} {p : PkD D G} (t : PkT F y mA p) (v) : IsUnit (p.Xo v).det := by
  obtain ⟨_, -, h⟩ := t.rr
  exact (h v).2

end GlobalTheory.Mem.R3.Rw.Bare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IoOfLeOneIff
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.TrueGeo

namespace GlobalTheory.ShFam.Pad

variable {F : Type} [Field F] [NumberField F]

theorem residueCharacteristic_prime (v : HeightOneSpectrum (𝓞 F)) : (resP v).Prime := by
  haveI := v.isMaximal
  haveI : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field _
  exact CharP.char_is_prime (𝓞 F ⧸ v.asIdeal) _

theorem residueCharacteristic_mem (v : HeightOneSpectrum (𝓞 F)) : ((resP v : ℕ) : 𝓞 F) ∈ v.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact ringChar.Nat.cast_ringChar

theorem ioOf_le_one_iff (p : ℕ) [Fact p.Prime] {v : HeightOneSpectrum (𝓞 F)} (hv : (p : 𝓞 F) ∈ v.asIdeal) (ε : Ext v) :
    ∀ a, ‖ioOf p ε a‖ ≤ 1 ↔ a ∈ ε.O := by
  obtain ⟨j, hj⟩ := GlobalTheory.PlaceBridge.exists_embedding (l := p) F (AlgebraicClosure F) v ε.O hv
    (GlobalTheory.TrueGeo.ExtConj.lies_over ε)
  have h : ∃ io : AlgebraicClosure F →+* ℂ_[p], ∀ a, ‖io a‖ ≤ 1 ↔ a ∈ ε.O :=
    ⟨(algebraMap (PadicAlgCl p) ℂ_[p]).comp j, fun a => by
      rw [hj, RingHom.comp_apply, ← PadicComplex.coe_eq, PadicComplex.norm_extends]⟩
  exact Classical.epsilon_spec h

theorem log_w_eq (p : ℕ) [hp : Fact p.Prime] {v : HeightOneSpectrum (𝓞 F)} (ε : Ext v)
    (io : AlgebraicClosure F →+* ℂ_[p]) (h : ∀ a, ‖io a‖ ≤ 1 ↔ a ∈ ε.O) (a : AlgebraicClosure F) :
    Real.log (ε.w a) = (-Real.log (ε.w p) / Real.log p) * Real.log ‖io a‖ := by
  let u : AbsoluteValue (AlgebraicClosure F) ℝ := (NormedField.toAbsoluteValue ℂ_[p]).comp io.injective
  have hu (x) : u x = ‖io x‖ := rfl
  have he : u.IsEquiv ε.w := AbsoluteValue.isEquiv_iff_lt_one_iff.2 fun x => by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · have h1 : u x⁻¹ ≤ 1 ↔ ε.w x⁻¹ ≤ 1 := by rw [hu, h, ε.mem_O]
      rw [map_inv₀, map_inv₀, inv_le_one₀ (u.pos hx), inv_le_one₀ (ε.w.pos hx)] at h1
      rw [← not_le, ← not_le, h1]
  obtain ⟨c, hc, hce⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.1 he
  have hw (x) : Real.log (ε.w x) = c * Real.log ‖io x‖ := by
    rw [← congrFun hce x, hu]
    rcases eq_or_ne x 0 with rfl | hx
    · simp [Real.zero_rpow hc.ne']
    · exact Real.log_rpow (norm_pos_iff.2 ((map_ne_zero io).2 hx)) c
  have hn : ‖io p‖ = (p : ℝ)⁻¹ := by
    rw [map_natCast, ← Padic.norm_p, ← PadicComplex.norm_extends']
    simp
  have hl : Real.log p ≠ 0 := (Real.log_pos (by exact_mod_cast hp.out.one_lt)).ne'
  rw [hw, hw, hn, Real.log_inv]
  field_simp

theorem ioOf_spec : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (ε : Ext v), ∃ hp : (resP v).Prime, haveI := Fact.mk hp; (∀ a, ‖ioOf (resP v) ε a‖ ≤ 1 ↔ a ∈ ε.O) ∧ ∀ a, Real.log (ε.w a) = (-Real.log (ε.w (resP v)) / Real.log (resP v)) * Real.log ‖ioOf (resP v) ε a‖ := fun _ _ _ v ε =>
  ⟨residueCharacteristic_prime v, by
    haveI := Fact.mk (residueCharacteristic_prime v)
    exact ⟨ioOf_le_one_iff _ (residueCharacteristic_mem v) ε, log_w_eq _ ε _ (ioOf_le_one_iff _ (residueCharacteristic_mem v) ε)⟩⟩

end GlobalTheory.ShFam.Pad
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TieInOfFwTie
section
noncomputable section

open NumberField

namespace GlobalTheory.OneMapRefObj

open _root_.Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.IndefR.Links Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem tieIn_of_fwTie {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, Formalism.MainNotions.WeightFamilies.Wt D ((i : ℕ) + 1)}
    {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec} (t : FWTie T R κ v₀) : TieIn T R κ v₀ :=
  ⟨t.laws, t.alg_eq, t.kap, t.hv₀, t.chiR, t.x0⟩

end GlobalTheory.OneMapRefObj
end
end

