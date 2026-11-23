module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0033
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import ReciprocityTheory.DualLattices.Bundle0015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0003
public import ReciprocityTheory.DualLattices.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NotIsUnitNatCastOfIsLocalHom
public import Development.AbelianVarietyTheory.BlockTheory.JetGauges.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StAvDefs
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0116
public import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ThetaLeMsupOfSetC
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0052
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0018
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0117
public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HalfPrincipalAndSplit
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons

namespace GlobalTheory.HalfGen

theorem factors_of_ncard_places (E : Type) [Field E] [NumberField E] (g : ℕ) (hg : g.Prime)
    (h : {v : HeightOneSpectrum (𝓞 E) | ((g : ℕ) : 𝓞 E) ∈ v.asIdeal}.ncard = Module.finrank ℚ E) :
    (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).card = Module.finrank ℚ E ∧
      (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).Nodup := by
  classical
  set I : Ideal (𝓞 E) := Ideal.span {(g : 𝓞 E)} with hI
  set s := UniqueFactorizationMonoid.normalizedFactors I with hs
  have hI0 : I ≠ ⊥ := by
    rw [hI, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hg.ne_zero
  have hprod : s.prod = I := Ideal.prod_normalizedFactors_eq_self hI0
  have hprime : ∀ P ∈ s, Prime P := fun P hP =>
    UniqueFactorizationMonoid.prime_of_normalized_factor P hP
  have hN : Ideal.absNorm I = g ^ Module.finrank ℚ E := by
    rw [hI, Ideal.absNorm_span_natCast, RingOfIntegers.rank]
  have hle : ∀ a ∈ s.map Ideal.absNorm, g ≤ a := by
    intro a ha
    obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.mp ha
    have hdvd : Ideal.absNorm P ∣ g ^ Module.finrank ℚ E := by
      rw [← hN, ← hprod]
      exact map_dvd _ (Multiset.dvd_prod hP)
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hg).mp hdvd
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero, Ideal.absNorm_eq_one_iff] at hk
      exact (hprime P hP).ne_one (by rw [hk, Ideal.one_eq_top])
    rw [hk]
    exact Nat.le_self_pow hk0 g
  have h1 : s.card ≤ Module.finrank ℚ E := by
    have := Multiset.pow_card_le_prod hle
    rw [← map_multiset_prod, hprod, hN, Multiset.card_map] at this
    exact (Nat.pow_le_pow_iff_right hg.one_lt).1 this
  have h2 : Module.finrank ℚ E ≤ s.toFinset.card := by
    rw [← h, ← Set.ncard_coe_finset]
    refine Set.ncard_le_ncard_of_injOn (fun v => v.asIdeal) (fun v hv => ?_)
      (fun v _ w _ e => HeightOneSpectrum.ext e) (Finset.finite_toSet _)
    rw [Finset.mem_coe, Multiset.mem_toFinset, hs, Ideal.mem_normalizedFactors_iff hI0]
    exact ⟨v.isPrime, (Ideal.span_singleton_le_iff_mem _).2 hv⟩
  have h3 := Multiset.toFinset_card_le s
  exact ⟨by omega, Multiset.toFinset_card_eq_card_iff_nodup.1 (by omega)⟩

theorem barE_piG {D : D7} (EX : ErrX D) (i : Fin 2) : barE D (EX.piG i) = piBarO EX i := by
  apply IsFractionRing.injective (𝓞 D.host.E) D.host.E
  exact barE_eq_conj D _

theorem half_principal_and_split : ∀ (D : D7) (T : Core D), LawsM T → ∀ EX : ErrX D,
 letI := T.Q.H.starRing
 (∃ α : 𝓞 D.host.E, α * star α = ((T.Q.l.M : ℕ) : 𝓞 D.host.E) ∧ T.Q.l.Mb = Ideal.span {star α}) ∧ (∀ i, star (EX.piG i) = piBarO EX i ∧ piBarO EX i * star (piBarO EX i) = ((D.host.g i : ℕ) : 𝓞 D.host.E)) ∧ ((∀ i, T.Q.l.Mb ≤ Ideal.span {piBarO EX i}) → T.Q.l.Mb = Ideal.span {piBarO EX 0 * piBarO EX 1}) ∧ ∀ (L : SizeData₂ D), ParameterChoice' D L → ∀ i, (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {((D.host.g i : ℕ) : 𝓞 D.host.E)})).card = Module.finrank ℚ D.host.E ∧ (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {((D.host.g i : ℕ) : 𝓞 D.host.E)})).Nodup := by
  intro D T h EX
  have hb : ∀ i, T.Q.H.bar (EX.piG i) = piBarO EX i := fun i => by rw [bar_core, barE_piG]
  have hbb : ∀ a, T.Q.H.bar (T.Q.H.bar a) = a := fun a => by rw [bar_core, bar_core, barE_barE]
  have hn : ∀ i, piBarO EX i * T.Q.H.bar (piBarO EX i) = ((D.host.g i : ℕ) : 𝓞 D.host.E) := fun i => by
    rw [← hb, hbb, mul_comm, hb]
    exact RPfVal.piG_mul_bar EX i
  have hM : T.Q.l.Mb = Ideal.span {piOf T EX 0 * piOf T EX 1} := by
    rw [← Ideal.span_singleton_mul_span_singleton, span_piOf T h, span_piOf T h, Mb_eq T h]
  have hp : ∀ i, piOf T EX i * T.Q.H.bar (piOf T EX i) = ((D.host.g i : ℕ) : 𝓞 D.host.E) := fun i => by
    rw [bar_core]; exact piOf_mul_barE T EX i
  have hpp : (piOf T EX 0 * piOf T EX 1) * T.Q.H.bar (piOf T EX 0 * piOf T EX 1) =
      ((D.host.g 0 : ℕ) : 𝓞 D.host.E) * ((D.host.g 1 : ℕ) : 𝓞 D.host.E) := by
    rw [map_mul, ← hp 0, ← hp 1]; ring
  refine ⟨⟨T.Q.H.bar (piOf T EX 0 * piOf T EX 1), ?_, ?_⟩, fun i => ⟨hb i, hn i⟩, fun ho => ?_, fun _ _ i => ?_⟩
  · show T.Q.H.bar _ * T.Q.H.bar (T.Q.H.bar _) = _
    rw [hbb, mul_comm, hpp, level_M T h, Nat.cast_mul]
  · show _ = Ideal.span {T.Q.H.bar (T.Q.H.bar _)}
    rw [hbb, hM]
  · have hcg : IsCoprime ((D.host.g 0 : ℕ) : 𝓞 D.host.E) ((D.host.g 1 : ℕ) : 𝓞 D.host.E) :=
      Nat.Coprime.cast ((Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne)
    rw [← hn 0, ← hn 1] at hcg
    have hc : IsCoprime (piBarO EX 0) (piBarO EX 1) := hcg.of_mul_left_left.of_mul_right_left
    have hd : ∀ i, piBarO EX i ∣ piOf T EX 0 * piOf T EX 1 := fun i =>
      Ideal.mem_span_singleton.1 (ho i (hM ▸ Ideal.mem_span_singleton_self _))
    obtain ⟨c, hcc⟩ := hc.mul_dvd (hd 0) (hd 1)
    have hg : ((D.host.g 0 : ℕ) : 𝓞 D.host.E) * ((D.host.g 1 : ℕ) : 𝓞 D.host.E) ≠ 0 :=
      mul_ne_zero (Nat.cast_ne_zero.2 (D.host.g_prime 0).ne_zero) (Nat.cast_ne_zero.2 (D.host.g_prime 1).ne_zero)
    have hu : c * T.Q.H.bar c = 1 := by
      apply mul_left_cancel₀ hg
      rw [_root_.mul_one]
      conv_rhs => rw [← hpp, hcc, map_mul, map_mul]
      rw [← hn 0, ← hn 1]
      ring
    rw [hM, hcc]
    exact Ideal.span_singleton_mul_right_unit (IsUnit.of_mul_eq_one _ hu) _
  · exact factors_of_ncard_places D.host.E (D.host.g i) (D.host.g_prime i) (D.nd.g_split i)

end GlobalTheory.HalfGen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HasFinColengthOfHasLen
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.PGsh.Up
open GlobalTheory.TorsionCompare NumberField
open scoped TensorProduct

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AvChartCompare

section Charts

variable {R : Type} [CommRing R]

variable {G : Over (Sp R)} {d : ℕ}

end Charts

section Series

variable {O : Type} [CommRing O] {d : ℕ}

variable {C : Type} [Field C] (v : Valuation C NNReal) [Algebra O C]

variable {v}

theorem hasLen_le_of_surjective (hv : v.Integers O) {M N : Type} [AddCommGroup M] [Module O M]
    [AddCommGroup N] [Module O N] (π : M →ₗ[O] N) (hπ : Function.Surjective π) {x y : NNReal}
    (hx : HasLen v O M x) (hy : HasLen v O N y) : x ≤ y := by
  have := isLocal_of_integers hv
  obtain ⟨m, c, ⟨e⟩, rfl⟩ := hx
  obtain ⟨n, b, ⟨e'⟩, rfl⟩ := hy
  let f := e'.toLinearMap ∘ₗ π ∘ₗ e.symm.toLinearMap
  have hf : Function.Surjective f := e'.surjective.comp (hπ.comp e.symm.surjective)
  let q : Fin m → ((j : Fin n) → O ⧸ Ideal.span {b j}) :=
    fun i => f (Pi.single i (1 : O ⧸ Ideal.span {c i}))
  have hq : Submodule.span O (Set.range q) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨z, rfl⟩ := hf z
    have hz : z = ∑ i, (Quotient.out (z i) : O) • Pi.single i (1 : O ⧸ Ideal.span {c i}) := by
      funext k
      rw [Finset.sum_apply, Finset.sum_eq_single k]
      · simp only [Pi.smul_apply, Pi.single_eq_same, Algebra.smul_def, _root_.mul_one,
          Ideal.Quotient.algebraMap_eq]
        exact (Ideal.Quotient.mk_out (z k)).symm
      · intro b _ hb
        simp [Pi.single_eq_of_ne' hb]
      · intro h; exact absurd (Finset.mem_univ k) h
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hz, map_sum]
    exact Submodule.sum_mem _ fun i _ => by
      rw [map_smul]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hT : ∀ k, ∑ i, (Matrix.diagonal c) k i • q i = 0 := by
    intro k
    rw [Finset.sum_eq_single k]
    · simp only [Matrix.diagonal_apply_eq, q, ← map_smul]
      have : c k • (Pi.single k (1 : O ⧸ Ideal.span {c k}) : (i : Fin m) → O ⧸ Ideal.span {c i}) =
          0 := by
        funext j
        by_cases hj : j = k
        · subst hj
          simp only [Pi.smul_apply, Pi.single_eq_same, Pi.zero_apply, Algebra.smul_def, _root_.mul_one,
            Ideal.Quotient.algebraMap_eq]
          exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
        · simp [Pi.single_eq_of_ne hj]
      rw [this, map_zero]
    · intro b _ hb; simp [Matrix.diagonal_apply_ne _ (Ne.symm hb)]
    · intro h; exact absurd (Finset.mem_univ k) h
  have h := det_mem_span_prod n b m q hq (Matrix.diagonal c) hT
  rw [Matrix.det_diagonal] at h
  simpa only [map_prod] using hv.le_of_dvd (Ideal.mem_span_singleton.1 h)

end Series

section Emb

variable {E : Type} [Field E] [NumberField E] {C : Type} [Field C] [CharZero C]
  {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C]

end Emb

section Places

variable {p : ℕ} [Fact p.Prime] {E : Type} [Field E] [NumberField E] [StarRing (𝓞 E)]
  {C : Type} [Field C] [CharZero C] {v : Valuation C NNReal} {O : Type} [CommRing O]
  [Algebra O C] [Algebra ℤ_[p] O]

variable {w : AvDefs.Place p (𝓞 E)} {P : Ideal (𝓞 E)}

end Places



end GlobalTheory.AvChartCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartDirectionsIsEigenBasisStatement
section
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_chart_directions_isEigenBasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (τ : E →+* ℂ) (τT : 𝓞 E →+* T.V), (∀ a, algebraMap T.V T.Fr (τT a) = io (embK c τ a)) → IsEigBasis Ch.actT τT (fun i : Fin (Dw.mult τ) => Ch.uvecT ⟨τ, i⟩) := by
  first | exact @GlobalTheory.CharDepth.isEigBasis_uvecT | exact GlobalTheory.CharDepth.isEigBasis_uvecT | (intros; apply GlobalTheory.CharDepth.isEigBasis_uvecT <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralFramedPointOfLevelMoveStatement
section
open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_framedPoint_of_level_move : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (g : (Dw.La →ₗ[𝓞 E] Dw.La) × (Dw.La →ₗ[𝓞 E] Dw.La)) (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra; ∀ y y' : FrPt Xo c T.Fr, levR (Xo := Xo) (c := c) g y y' → Integral T io y → Integral T io y' := by
  first | exact @GlobalTheory.FormTies.LevelMove.integral_of_levR | exact GlobalTheory.FormTies.LevelMove.integral_of_levR | (intros; apply GlobalTheory.FormTies.LevelMove.integral_of_levR <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LargePrimePackagesDepthNonpos
section
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.DIV
open scoped BigOperators

namespace GlobalTheory.GoodDepth.Zero

theorem cut (K s B : ℕ) (e : ℕ → ℕ) : ∃ pc : Fin s → ℕ → ℕ,
    (∀ u, ∑ k ∈ Finset.Icc 1 K, pc u k ≤ B) ∧
    (∑ k ∈ Finset.Icc 1 K, e k ≤ s * B → (∀ k, e k ≠ 0 → 1 ≤ k ∧ k ≤ K) → ∀ k, ∑ u, pc u k = e k) := by
  by_cases h : ∑ k ∈ Finset.Icc 1 K, e k ≤ s * B
  · obtain ⟨pc, h1, h2, h3⟩ := GlobalTheory.exists_cut_columns_bounded_width K s B e h
    refine ⟨pc, h2, fun _ hsupp k => ?_⟩
    by_cases hk : k ∈ Finset.Icc 1 K
    · exact h1 k hk
    · have hek : e k = 0 := by
        by_contra hne
        exact hk (Finset.mem_Icc.mpr (hsupp k hne))
      rw [hek]
      exact Finset.sum_eq_zero fun u _ => h3 u k hk
  · exact ⟨fun _ _ => 0, fun _ => by simp, fun h' => absurd h' h⟩

theorem monAl_le_first (K rk : ℕ) (e : ℕ → ℕ) (ρ : ℕ) :
    monAl K rk e ρ ≤ ∑ k ∈ Finset.Icc 1 K, e k := by
  unfold monAl
  apply Finset.sum_le_sum_of_subset
  intro k hk
  simp only [Finset.mem_Icc] at hk ⊢
  exact ⟨by omega, hk.2.trans (min_le_left _ _)⟩

theorem zero_of_pkg (hM : RF.MONSupply) (P : RF.Par) (l : ℕ) (Pk : RF.PkgZero P l) : Pk.ν ≤ 0 := by
  classical
  rcases Nat.eq_zero_or_pos l with hl | hl
  · have hz : ∀ z ∈ Pk.Z, ∀ g a k, Pk.ga z g a k = 0 := by
      intro z hz g a k
      by_contra hne
      have hs := Pk.supp z hz g a k hne
      have h0 : Pk.s * (l - 1) = 0 := by simp [hl]
      have hf := (Pk.first z hz g a).trans h0.le
      exact hne ((Finset.sum_eq_zero_iff.mp (Nat.le_zero.mp hf)) k
        (Finset.mem_Icc.mpr ⟨hs.1, hs.2.2⟩))
    have h := Pk.val (fun _ => []) (by simp) (by simp)
      (by intro o ho g a k; simp [hz o ho g a k])
    simpa using h
  · have hcut : ∀ z g a, ∃ pc : Fin Pk.s → ℕ → ℕ,
        (∀ u, ∑ k ∈ Finset.Icc 1 Pk.K, pc u k ≤ l - 1) ∧
        (z ∈ Pk.Z → ∀ k, ∑ u, pc u k = Pk.ga z g a k) := by
      intro z g a
      obtain ⟨pc, h1, h2⟩ := cut Pk.K Pk.s (l - 1) (Pk.ga z g a)
      exact ⟨pc, h1, fun hz => h2 (Pk.first z hz g a)
        fun k hk => ⟨(Pk.supp z hz g a k hk).1, (Pk.supp z hz g a k hk).2.2⟩⟩
    choose pc hpc1 hpc2 using hcut
    let blk : P.Pl → Fin 2 × Fin Pk.s → RF.GlobalTheory P.d × ℝ :=
      fun z q => (RF.GlobalTheory.mon q.1 (fun a => pc z q.1 a q.2) Pk.K, 0)
    let L : P.Pl → List (RF.GlobalTheory P.d × ℝ) :=
      fun z => (Finset.univ : Finset (Fin 2 × Fin Pk.s)).toList.map (blk z)
    have hsum0 : ∑ o ∈ Pk.Z, ((L o).map Prod.snd).sum = 0 := by
      simp [L, blk]
    refine (Pk.val L ?_ ?_ ?_).trans hsum0.le
    · intro o _ p hp
      simp only [L, List.mem_map, Finset.mem_toList] at hp
      obtain ⟨q, -, rfl⟩ := hp
      refine (hM Pk.R.C Pk.R.V P.d (Pk.R.I o) (Pk.R.J o) (Pk.R.X o) (Pk.R.F o) q.1
        (fun a => pc o q.1 a q.2) Pk.K).2 ?_
      intro a ρ
      rw [Pk.R.hVl]
      have h1 := (monAl_le_first Pk.K ((Pk.R.X o).rkF q.1 a) (pc o q.1 a q.2) ρ).trans (hpc1 o q.1 a q.2)
      omega
    · have hrow : ∀ o, ((L o).map fun p => p.1.what₂ (Pk.R.X o).n).sum = 2 * Pk.s * Pk.K := by
        intro o
        simp only [L, List.map_map]
        rw [Finset.sum_map_toList]
        simp [blk, RF.GlobalTheory.what₂]
      rw [Finset.sum_congr rfl fun o _ => hrow o, Finset.sum_const, smul_eq_mul]
      calc Pk.Z.card * (2 * Pk.s * Pk.K) = 2 * Pk.K * Pk.s * Pk.Z.card := by ring
        _ ≤ Pk.nW := Pk.what₂
    · intro o ho g a k
      have hw : ∀ q : Fin 2 × Fin Pk.s, (blk o q).1.wt (Pk.R.X o) g a k =
          if q.1 = g then (if 1 ≤ k ∧ k ≤ min Pk.K ((Pk.R.X o).rkF g a) then pc o g a q.2 k else 0)
          else 0 := by
        rintro ⟨g', u⟩
        by_cases hg : g' = g
        · subst hg
          simp [blk, RF.GlobalTheory.wt]
        · simp [blk, RF.GlobalTheory.wt, hg, Ne.symm hg]
      calc ((L o).map fun p => p.1.wt (Pk.R.X o) g a k).sum
          = ∑ q : Fin 2 × Fin Pk.s, (blk o q).1.wt (Pk.R.X o) g a k := by
            simp only [L, List.map_map]
            rw [Finset.sum_map_toList]
            rfl
        _ = ∑ q : Fin 2 × Fin Pk.s, if q.1 = g then
              (if 1 ≤ k ∧ k ≤ min Pk.K ((Pk.R.X o).rkF g a) then pc o g a q.2 k else 0) else 0 :=
            Finset.sum_congr rfl fun q _ => hw q
        _ = ∑ u : Fin Pk.s,
              (if 1 ≤ k ∧ k ≤ min Pk.K ((Pk.R.X o).rkF g a) then pc o g a u k else 0) := by
            rw [Fintype.sum_prod_type, Finset.sum_eq_single g]
            · simp
            · intro b _ hb
              simp [hb]
            · simp
        _ = Pk.ga o g a k := by
            by_cases hk : 1 ≤ k ∧ k ≤ min Pk.K ((Pk.R.X o).rkF g a)
            · simp only [if_pos hk]
              exact hpc2 o g a ho k
            · simp only [if_neg hk, Finset.sum_const_zero]
              symm
              by_contra hne
              have hs := Pk.supp o ho g a k hne
              exact hk ⟨hs.1, le_min hs.2.2 hs.2.1⟩

theorem zero_of_pkgC (hM : RF.MONSupply) (P : RF.Par) (l : ℕ) (Pk : RF.PkgZeroC P l) : Pk.ν ≤ 0 := by
  classical
  rcases Nat.eq_zero_or_pos l with hl | hl
  · have hz : ∀ z σ k, Pk.gaC z σ k = 0 := by
      intro z σ k
      by_contra hne
      have hs := Pk.supp z σ k hne
      have h0 : Pk.s * (l - 1) = 0 := by simp [hl]
      have hf := (Pk.first z σ).trans h0.le
      exact hne ((Finset.sum_eq_zero_iff.mp (Nat.le_zero.mp hf)) k
        (Finset.mem_Icc.mpr ⟨hs.1, hs.2.2⟩))
    have h := Pk.val (fun _ => []) (by simp) (by simp) (by simp)
      (by intro o σ k; simp [hz o σ k])
    simpa using h
  · have hcut : ∀ z σ, ∃ pc : Fin Pk.s → ℕ → ℕ,
        (∀ u, ∑ k ∈ Finset.Icc 1 Pk.K, pc u k ≤ l - 1) ∧ (∀ k, ∑ u, pc u k = Pk.gaC z σ k) := by
      intro z σ
      obtain ⟨pc, h1, h2⟩ := cut Pk.K Pk.s (l - 1) (Pk.gaC z σ)
      exact ⟨pc, h1, h2 (Pk.first z σ)
        fun k hk => ⟨(Pk.supp z σ k hk).1, (Pk.supp z σ k hk).2.2⟩⟩
    choose pc hpc1 hpc2 using hcut
    let ee : P.Pl → ZMod 2 × Fin Pk.s → ZMod 2 → ℕ → ℕ :=
      fun z q a k => if a = q.1 then pc z q.1 q.2 k else 0
    let blk : P.Pl → ZMod 2 × Fin Pk.s → RF.GlobalTheory 2 × ℝ :=
      fun z q => (RF.GlobalTheory.mon 0 (ee z q) Pk.K, 0)
    let L : P.Pl → List (RF.GlobalTheory 2 × ℝ) :=
      fun z => (Finset.univ : Finset (ZMod 2 × Fin Pk.s)).toList.map (blk z)
    have hsum0 : ∑ o, ((L o).map Prod.snd).sum = 0 := by
      simp [L, blk]
    refine (Pk.val L ?_ ?_ ?_ ?_).trans hsum0.le
    · intro o p hp
      simp only [L, List.mem_map, Finset.mem_toList] at hp
      obtain ⟨q, -, rfl⟩ := hp
      refine (hM Pk.R.C Pk.R.V 2 (Pk.R.I o) (Pk.R.J o) (Pk.R.X o) (Pk.R.F o) 0 (ee o q) Pk.K).2 ?_
      intro a ρ
      rw [Pk.R.hVl]
      have h1 : ∑ k ∈ Finset.Icc 1 Pk.K, ee o q a k ≤ l - 1 := by
        by_cases ha : a = q.1
        · simpa [ee, ha] using hpc1 o q.1 q.2
        · simp [ee, ha]
      have h2 := (monAl_le_first Pk.K ((Pk.R.X o).rkF 0 a) (ee o q a) ρ).trans h1
      omega
    · intro o p hp g e N hpe
      simp only [L, List.mem_map, Finset.mem_toList] at hp
      obtain ⟨q, -, rfl⟩ := hp
      obtain ⟨-, rfl, -⟩ := RF.GlobalTheory.mon.inj hpe
      exact ⟨q.1, fun a k ha => by simp [ee, ha]⟩
    · have hrow : ∀ o, ((L o).map fun p => p.1.what₂ (Pk.R.X o).n).sum = 2 * Pk.s * Pk.K := by
        intro o
        simp only [L, List.map_map]
        rw [Finset.sum_map_toList]
        simp [blk, RF.GlobalTheory.what₂]
      rw [Finset.sum_congr rfl fun o _ => hrow o, Finset.sum_const, smul_eq_mul, Finset.card_univ]
      calc 2 * (Fintype.card P.Pl * (2 * Pk.s * Pk.K)) = 4 * Pk.K * Pk.s * Fintype.card P.Pl := by ring
        _ ≤ Pk.nW := Pk.what₂
    · intro o σ k
      have hw : ∀ q : ZMod 2 × Fin Pk.s,
          (blk o q).1.wt (Pk.R.X o) 0 σ k + (blk o q).1.wt (Pk.R.X o) 1 (σ + 1) k =
          if q.1 = σ then (if 1 ≤ k ∧ k ≤ min Pk.K ((Pk.R.X o).rkF 0 σ) then pc o σ q.2 k else 0)
          else 0 := by
        rintro ⟨a, u⟩
        by_cases ha : a = σ
        · subst ha
          simp [blk, ee, RF.GlobalTheory.wt]
        · simp [blk, ee, RF.GlobalTheory.wt, ha, Ne.symm ha]
      calc ((L o).map fun p => p.1.wt (Pk.R.X o) 0 σ k + p.1.wt (Pk.R.X o) 1 (σ + 1) k).sum
          = ∑ q : ZMod 2 × Fin Pk.s,
              ((blk o q).1.wt (Pk.R.X o) 0 σ k + (blk o q).1.wt (Pk.R.X o) 1 (σ + 1) k) := by
            simp only [L, List.map_map]
            rw [Finset.sum_map_toList]
            rfl
        _ = ∑ q : ZMod 2 × Fin Pk.s, if q.1 = σ then
              (if 1 ≤ k ∧ k ≤ min Pk.K ((Pk.R.X o).rkF 0 σ) then pc o σ q.2 k else 0) else 0 :=
            Finset.sum_congr rfl fun q _ => hw q
        _ = ∑ u : Fin Pk.s,
              (if 1 ≤ k ∧ k ≤ min Pk.K ((Pk.R.X o).rkF 0 σ) then pc o σ u k else 0) := by
            rw [Fintype.sum_prod_type, Finset.sum_eq_single σ]
            · simp
            · intro b _ hb
              simp [hb]
            · simp
        _ = Pk.gaC o σ k := by
            by_cases hk : 1 ≤ k ∧ k ≤ min Pk.K ((Pk.R.X o).rkF 0 σ)
            · simp only [if_pos hk]
              exact hpc2 o σ k
            · simp only [if_neg hk, Finset.sum_const_zero]
              symm
              by_contra hne
              have hs := Pk.supp o σ k hne
              exact hk ⟨hs.1, le_min hs.2.2 hs.2.1⟩

end GlobalTheory.GoodDepth.Zero

theorem GlobalTheory.GoodDepth.zeroBd : GlobalTheory.GoodDepth.ZeroBd :=
  ⟨fun P l Pk => GlobalTheory.GoodDepth.Zero.zero_of_pkg _root_.GlobalTheory.MonBlock.monSupply.2 P l Pk,
    fun P l Pk => GlobalTheory.GoodDepth.Zero.zero_of_pkgC _root_.GlobalTheory.MonBlock.monSupply.2 P l Pk⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ScaledThetaTranslationQuotientEllipticStatement
section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scaledThetaTranslationQuotient_elliptic : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]) (θ : ℂ → ℂ), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.MChart ω → IsTh d θ → ∀ (t : ℂ) (s : ℕ), 0 < s → Nat.Coprime s q → InOK d ((s : ℂ) * t) → let φ : ℂ → ℂ := fun z => U1 d t θ ((s : ℂ) * z) / θ ((s : ℂ) * z); Ell M.L φ ∧ AnalyticAt ℂ φ 0 ∧ (∀ p, θ ((s : ℂ) * p) ≠ 0 → AnalyticAt ℂ φ p) ∧ (∀ p r, PrimeTo d q r → ¬ InOK d (r - 1 / 2) → θ ((s : ℂ) * p + r) = 0 → ¬ M.Small p) ∧ Bdd (hat M.ι (C ω * logS) φ) := by
  first | exact @GlobalTheory.MomOne.ScaledQuot.scaled_quotient_elliptic | exact GlobalTheory.MomOne.ScaledQuot.scaled_quotient_elliptic | (intros; apply GlobalTheory.MomOne.ScaledQuot.scaled_quotient_elliptic <;> assumption)
end

