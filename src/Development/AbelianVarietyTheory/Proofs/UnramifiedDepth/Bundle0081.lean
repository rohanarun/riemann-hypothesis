module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0179
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0217
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UniversalStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartFormalBiext
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IntegralFramedPointModelPolarisedGenericFibreStatement
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0072
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0015
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0012
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
public import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsFormalGroupJetsChart
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IntegralGermEqGaugedFormalGroupLawExpIntegral
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0005
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ValuationIntegersPadicComplete
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsLevelOverIntegers
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0027
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
public import ReciprocityTheory.DualLattices.Bundle0028
public import ReciprocityTheory.DualLattices.Bundle0014
public import ReciprocityTheory.DualLattices.Bundle0035
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.DualLattices.Bundle0031
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.BiextensionNondegenerateModMaximalIdealIntegralC
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

namespace GlobalTheory.AlphaPair

section Steps

variable {Ω : Type} [Field Ω] {p : ℕ} [Fact p.Prime] [CharP Ω p] {S S' : Scheme.{0}} {s : Sp Ω ⟶ S} {s' : Sp Ω ⟶ S'}
  {G : Over S} [GrpObj G] {B : Over S'} [GrpObj B] {X : Type} [AddCommGroup X] {τ : PtHom s s' G B} {io : TorHom s G X}

theorem pow_p_of_sq {A : Type} [CommRing A] {e : A} (he : e ^ 2 = 0) : e ^ p = 0 :=
  pow_eq_zero_of_le (Fact.out : p.Prime).two_le he

theorem eps_pow : (DualNumber.eps : DualNumber Ω) ^ p = 0 :=
  pow_p_of_sq (by rw [pow_two, DualNumber.eps_mul_eps])

theorem eq_one_of_torus (h : IsTorExt s s' G B X τ io) {g : Fam s G} (hg : IsAlpha p s G g)
    (h1 : τ _ (g (DualNumber Ω) DualNumber.eps) = 1) : g (DualNumber Ω) DualNumber.eps = 1 := by
  classical
  have h2 := GlobalTheory.T.eq_one_of_tangent_vector_eq_one Ω p S' s' B _ (hg.map h) h1
  have h3 : ∀ (A : Type) [CommRing A] [Algebra Ω A] (a : A), ∃ χ, a ^ p = 0 → io A χ = g A a := fun A _ _ a => by
    by_cases ha : a ^ p = 0
    · obtain ⟨χ, hχ⟩ := (h.2.2.2.1 A _).1 (h2 A a ha)
      exact ⟨χ, fun _ => hχ⟩
    · exact ⟨1, fun k => absurd k ha⟩
  choose χ hχ using h3
  have h4 : χ (DualNumber Ω) DualNumber.eps = 1 := MonoidHom.ext fun x =>
    _root_.GlobalTheory.AlphaChar.char_eq_one Ω p (fun A _ _ a => χ A a x) (fun A A' _ _ _ _ f a ha => by
      have ha' : f a ^ p = 0 := by rw [← map_pow, ha, map_zero]
      have : χ A' (f a) = (Units.map (f : A →* A')).comp (χ A a) :=
        h.2.2.1 A' (by rw [hχ A' _ ha', h.2.1, hχ A a ha, hg.1 A A' f a ha])
      exact DFunLike.congr_fun this x) (fun A _ _ a a' ha ha' => by
      have hs : (a + a') ^ p = 0 := by
        rcases subsingleton_or_nontrivial A with _ | _
        · exact Subsingleton.elim _ _
        · have := charP_of_injective_algebraMap (algebraMap Ω A).injective p
          rw [add_pow_char, ha, ha', add_zero]
      have : χ A (a + a') = χ A a * χ A a' :=
        h.2.2.1 A (by rw [map_mul, hχ A _ hs, hχ A a ha, hχ A a' ha', hg.2 A a a' ha ha'])
      exact DFunLike.congr_fun this x) _ _ eps_pow
  rw [← hχ _ _ eps_pow, h4, map_one]

variable [IsCommMonObj G] [IsCommMonObj B] {L : RigLB G} {c : CubicalStr G L} {M : RigLB B} {c' : CubicalStr B M}

theorem Orth.map [Module.Free ℤ X] [Module.Finite ℤ X] (h : IsTorExt s s' G B X τ io) (ht : Transfer p c c' τ)
    {g : Fam s G} (hg : IsAlpha p s G g) (ho : Orth p s G c g) : Orth p s' B c' (fun A _ _ a => τ A (g A a)) := by
  intro A _ _ π hπ e he y hy hyp
  have hp := (Fact.out : p.Prime).ne_zero
  obtain ⟨x, hx, rfl⟩ := h.2.2.2.2 A π hπ y hy
  obtain ⟨χ, hχ⟩ := (h.2.2.2.1 A (x ^ p)).1 (by rw [map_pow, hyp])
  have h1 : (Units.map (π : A →* Ω)).comp χ = 1 :=
    h.2.2.1 Ω (by rw [h.2.1, hχ, MonObj.comp_pow, hx, one_pow, map_one])
  obtain ⟨A', _, _, f, π', χ', hf, hc, hn, h2, h3⟩ := _root_.GlobalTheory.TorusRoot.exists_root_character Ω p X A π hπ χ fun a =>
    congrArg Units.val (DFunLike.congr_fun h1 a)
  have h4 : (Units.map (π' : A' →* Ω)).comp χ' = 1 := MonoidHom.ext fun a => Units.ext (h2 a)
  have k := ht A' _ _ (ho A' π' hn (f e) (by rw [← map_pow, he, map_zero]) ((homAt s f ≫ x) * (io A' χ')⁻¹)
    (by rw [MonObj.comp_mul, GrpObj.comp_inv, ← h.2.1, h4, map_one, inv_one, _root_.mul_one, ← Category.assoc, hom_comp,
      hc, hx])
    (by rw [mul_pow, inv_pow, ← map_pow, h3, h.2.1, hχ, MonObj.comp_pow, mul_inv_cancel]))
  rw [hg.1 A A' f e (pow_p_of_sq he), map_mul, map_inv, (h.2.2.2.1 A' _).2 ⟨χ', rfl⟩, inv_one, _root_.mul_one,
    h.1, h.1] at k
  exact cubWeil_of_injective f hf ((hg.map h).pow_eq_one hp (pow_p_of_sq he)) hyp k

theorem NonDeg.of_torExt [Module.Free ℤ X] [Module.Finite ℤ X] (h : IsTorExt s s' G B X τ io) (ht : Transfer p c c' τ)
    (hB : NonDeg p s' B c') : NonDeg p s G c := fun _ hg ho =>
  eq_one_of_torus h hg (hB _ (hg.map h) (ho.map h ht hg))

theorem NonDeg.of_perf [IsAlgClosed Ω] (hf : IsFinite ((𝟙 G) ^ p : G ⟶ G).left) (hP : Perf p G c) :
    NonDeg p s G c := by
  intro g hg ho
  have hp := (Fact.out : p.Prime).ne_zero
  have : Module.Finite Ω (DualNumber Ω) := inferInstanceAs (Module.Finite Ω (Ω × Ω))
  refine hP _ _ (hg.pow_eq_one hp eps_pow) (_root_.GlobalTheory.AlphaPair.cubWeil_one_of_local_artinian Ω S s G L c p hf (DualNumber Ω) _ (hg.pow_eq_one hp eps_pow)
    fun A _ _ π hπ f y hy => ?_)
  have he : f DualNumber.eps ^ 2 = 0 := by rw [← map_pow, pow_two, DualNumber.eps_mul_eps, map_zero]
  have hx : (homAt s π ≫ y) ^ p = 1 := by rw [← MonObj.comp_pow, hy, MonObj.comp_one]
  have k₁ := _root_.GlobalTheory.AlphaPair.cubWeil_alpha_rational Ω p S s G L c g hg _ hx A _ (pow_p_of_sq he)
  have k₂ := ho A π hπ _ he (y * (homAt s (Algebra.ofId Ω A) ≫ homAt s π ≫ y)⁻¹)
    (by rw [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc (homAt s π), hom_comp,
      Subsingleton.elim (π.comp (Algebra.ofId Ω A)) (AlgHom.id Ω Ω), hom_id, Category.id_comp, mul_inv_cancel])
    (by rw [mul_pow, inv_pow, hy, k₁.2.1, inv_one, _root_.mul_one])
  have k := cubWeil_mul_right k₂ k₁
  rwa [inv_mul_cancel_right, hg.1 _ A f _ eps_pow] at k

end Steps

theorem perf_of_polAV {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] [CharZero O] (P : Out.PolAV (Sp O))
    [IsCommMonObj P.A] [IsNoetherianRing O] (L : RigLB P.A) (hL : L.L = P.L) (c : CubicalStr P.A L) {n : ℕ} (hn : 1 ≤ n) :
    IsFinite ((𝟙 P.A) ^ n : P.A ⟶ P.A).left ∧ Perf n P.A c := by
  have hl := GlobalTheory.firstFiveLaws.1
  let K := AlgebraicClosure (FractionRing O)
  have hi : Function.Injective (algebraMap O K) := by
    rw [IsScalarTower.algebraMap_eq O (FractionRing O) K]
    exact (algebraMap (FractionRing O) K).injective.comp (IsFractionRing.injective O _)
  have : CharZero K := charZero_of_injective_algebraMap hi
  have hnK : (n : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  obtain ⟨f₁, f₂, f₃⟩ := _root_.GlobalTheory.MulAmple.finite_flat_surjective_pow hl O P.A P.isAb P.L P.isLB P.ample n hn
  refine ⟨f₁, _root_.GlobalTheory.cubWeil_perfect_of_generic O K hi P.A P.g P.smoothDim L c n hn f₁ f₂
    ((hl.mulN _ P n hn).2.2.2.2 K _ hnK) fun y hy hp => ?_⟩
  have ht := CubNondeg.main hl _ P.A P.isAb L c K _ n hnK f₁ f₂ f₃ y hy hp
  rw [hL] at ht
  obtain ⟨u, hu⟩ := ht
  exact P.ktriv K _ y fun _ => ⟨⊤, trivial, _, LB.isGen_genPull _ u hu _⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem nonDeg_of_polAt {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (hV : GlobalTheory.LN.CDvr V) (t : SAB H (Sp V))
    (ht : GlobalTheory.LN.PolAt t (Out.jK V)) {Ω : Type} [Field Ω] [IsAlgClosed Ω] (p : ℕ) [Fact p.Prime] [CharP Ω p]
    (β : V →+* Ω) (hβ : ∀ a ∈ maximalIdeal V, β a = 0) : NonDeg p (spMap β) t.G t.cub := by
  obtain ⟨W, _, _, _, f, β', t', m, hW, hf, hβ', ht', hs⟩ := _root_.GlobalTheory.SplitPoint.exists_split_extension E H V hV t ht Ω β hβ
  obtain ⟨τ, io, h₁, h₂⟩ := _root_.GlobalTheory.AlphaPair.exists_isTorExt_pull E H _ _ _ t t' m Ω (spMap β) (spMap β') (by
    rw [← hf]; exact (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom β')).symm) p
  refine NonDeg.of_torExt h₁ h₂ ?_
  obtain ⟨P, -⟩ := GlobalTheory.LN.uDvrSt_holds E H W hW t' ht' hs
  obtain ⟨τ', io', k₁, k₂⟩ := _root_.GlobalTheory.TorExtPoints.exists_isTorExt W _ P.D.toPre t'.G (P.U.gt 0) Ω β' hβ'
  have k₃ := _root_.GlobalTheory.AlphaPair.transfer_of_unif W _ P.D P.A t'.G P.U.toUnifPre Ω β' hβ' τ' k₂ p
  have := hW.1
  have := hW.2.2
  obtain ⟨f₁, f₂⟩ := perf_of_polAV P.D.toPre.P ⟨_, P.D.toPre.rig, P.D.toPre.P.isLB, P.D.toPre.rig_gen⟩ rfl
    P.D.toPre.cub (Fact.out : p.Prime).one_le
  have k₄ := NonDeg.of_torExt k₁ k₃ (NonDeg.of_perf f₁ f₂)
  have key : ∀ (L : RigLB t'.G) (_ : L = t'.PP) (c : CubicalStr t'.G L), NonDeg p (spMap β') t'.G c →
      NonDeg p (spMap β') t'.G t'.cub := by
    rintro L rfl c hc
    rwa [PtGermCompare.cubical_unique (PtGermCompare.surjective_cube P.U.toUnifPre) t'.cub c]
  exact key _ P.bundle _ k₄

theorem ev_map_eq_one {R R' : Type} [CommRing R] [CommRing R'] (β : R →+* R') {d : ℕ} (f : PS R 3 d)
    (a : Fin 3 → Germ.Pt R 2 d) (a' : Fin 3 → Germ.Pt R' 2 d) (ha : ∀ j i, MvPowerSeries.constantCoeff (a j i) = 0)
    (h' : ∀ j i, a' j i = MvPowerSeries.map β (a j i)) (h : ev a f = 1) : ev a' (MvPowerSeries.map β f) = 1 := by
  have := MvPowerSeries.map_subst (a := fun q : Fin 3 × Fin d => a q.1 q.2)
    (MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => ha q.1 q.2) (h := β) f
  rw [show MvPowerSeries.subst (fun q : Fin 3 × Fin d => a q.1 q.2) f = 1 from h, map_one] at this
  unfold ev
  simp only [h']
  exact this.symm

theorem ndg_at_chart : ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) [StarRing (NumberField.RingOfIntegers E)], NondegenerateCharts Xo c := by
  intro E _ _ _ H Dw l Xo c inst hstar T io y C3 C _ _ V ι' hι k Y hY
  obtain rfl := PowGerm.starSt E H inst hstar
  letI := H.starRing
  letI := io.toAlgebra
  by_contra hN
  obtain ⟨Ω, _, _, _, ρ, hρ⟩ := _root_.GlobalTheory.AlphaPair.ResField.exists_residueField C V Y.algClosed
  obtain ⟨j, hj, hjm⟩ := _root_.GlobalTheory.embOK_exists_ringHom T C V ι' hι
  have : Fact V.l.Prime := ⟨V.l_prime⟩
  obtain ⟨BT, hF, -, h1, h2, -⟩ := integralChart_formalBiext E H Dw l Xo c T io y C3
  have hF0 : ∀ i, MvPowerSeries.constantCoeff (C3.FT i) = 0 := fun i => hF ▸ BT.G.const i
  have e : V.RR.subtype.comp j = ι'.comp (algebraMap T.V T.Fr) := RingHom.ext hj
  have hD := _root_.GlobalTheory.AlphaPair.Reduce.degenerate_of_not_ndg C V _ _ Y T.V j C3.FT C3.ph2T hF0
    (fun i => by rw [hY.F, e, MvPowerSeries.map_comp]; exact congrArg _ (C3.gen.1.1 i))
    (by rw [hY.ph2, e, MvPowerSeries.map_comp]; exact congrArg _ C3.gen.1.2.2.2.1) Ω ρ hρ hN
  obtain ⟨P, hP, hL⟩ := _root_.GlobalTheory.AlphaPair.exists_jetPt E H T.V C3.I.G _ _ _ _ _ _ C3.chartT hF0 Ω (ρ.comp j)
  refine GlobalTheory.T.not_nondegenerate_of_degenerate_series_direction Ω V.l _ _ C3.I.G.G _ C3.I.G.cub _ _ (MvPowerSeries.map (ρ.comp j) C3.ph1T) _ P
    (fun i => by rw [MvPowerSeries.constantCoeff_map, hF0, map_zero]) ?_ ?_ ?_ hL
    (_root_.GlobalTheory.AlphaPair.jetUniv E H T.V C3.I.G _ _ (PowGerm.univSt_holds E H Dw l Xo c T io y C3) Ω _ P hP)
    (_root_.GlobalTheory.AlphaPair.Cube.isPtCube_of_isFrame E H T.V C3.I.G _ _ _ _ _ _ _ _ _ C3.frameT hF0 Ω _ P hP) hD
    (nonDeg_of_polAt ⟨T.dvr, T.cpl, T.ch0⟩ C3.I.G (GlobalTheory.T.integralFramedPoint_model_polarised_generic_fibre E H Dw l Xo c T io y.1 C3.I) V.l _
      fun a ha => (hρ _).2 (hjm a ha))
  · refine ev_map_eq_one _ _ _ _ ?_ ?_ (h1 ▸ BT.cocycleLeft_zero_fst) <;> intro a b <;> fin_cases a <;> simp [pt]
  · refine ev_map_eq_one _ _ _ _ ?_ ?_ (h1 ▸ BT.cocycleLeft_zero_snd) <;> intro a b <;> fin_cases a <;> simp [pt]
  · refine ev_map_eq_one _ _ _ _ ?_ ?_ (h2 ▸ BT.cocycleRight_zero_fst) <;> intro a b <;> fin_cases a <;> simp [pt]

end GlobalTheory.AlphaPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsFiniteExtPelUnif
section
noncomputable section

namespace GlobalTheory.ChartCharacters

section Unif

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.UnifAfterExt

theorem exists_split_baseChange (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (maximalIdeal W) W] (G : Over (Sp W)) [GrpObj G] (hG : IsSemiAbelian G) :
    ∃ (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsDiscreteValuationRing W')
      (_ : IsAdicComplete (maximalIdeal W') W') (_ : Algebra W W'),
      Module.Finite W W' ∧ Function.Injective (algebraMap W W') ∧
      ∃ S : SplitExt (Sp (ResidueField W')), S.IsGt ((Over.pullback (spMap (residue W'))).obj
        ((Over.pullback (spMap (algebraMap W W'))).obj G)) := by
  have h₀ : IsSemiAbelian ((Over.pullback (spMap (residue W))).obj G) := IsSemiAbelian.pullback _ G hG
  obtain ⟨k', _, _, hk, E, ⟨d⟩⟩ := exists_finite_split _ h₀
  obtain ⟨W', i1, i2, i3, i4, i5, hf, hi, e, he⟩ := _root_.GlobalTheory.exists_finite_dvr_residueField_ringHom W k'
  refine ⟨W', i1, i2, i3, i4, i5, hf, hi, ?_⟩
  have key : (e.comp (algebraMap (ResidueField W) k')).comp (residue W) =
      (residue W').comp (algebraMap W W') := RingHom.ext he
  obtain ⟨j, hj, -⟩ := grpPullback_iso
    (((isGrpPullback_pullback _ (spMap e)).comp
      ((isGrpPullback_pullback _ (spMap (algebraMap (ResidueField W) k'))).comp
        (isGrpPullback_pullback G (spMap (residue W))))).congr
      (f' := spMap (residue W') ≫ spMap (algebraMap W W'))
      (by rw [← Category.assoc, ← spMap_comp, ← spMap_comp, ← spMap_comp, key]) rfl)
    ((isGrpPullback_pullback _ (spMap (residue W'))).comp (isGrpPullback_pullback G (spMap (algebraMap W W'))))
  exact ⟨_, isGt_of_iso j (GtBaseChange.isGt_extBC (spMap e) E _ d)⟩

theorem exists_finite_ext_pelUnif {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} (Xo : Moduli Dw l) (T : Formalism.L2.Pj.CDVR) (t : SAB H (Sp T.V)) (tK : SAB H (Sp T.Fr))
    (mK : SABMap tK t (jK T.V)) (x : Sp T.Fr ⟶ Xo.X) (mx : SABMap tK Xo.univ.t x) :
    ∃ (T' : Formalism.L2.Pj.CDVR) (φ : T.V →+* T'.V) (t' : SAB H (Sp T'.V)) (_ : SABMap t' t (spMap φ)),
      Function.Injective φ ∧ φ.Finite ∧ Nonempty (PELUnif (maximalIdeal T'.V) t') := by
  obtain ⟨W, _, _, _, hc, _, hf, hi, hS⟩ := exists_split_baseChange T.V t.G t.semi
  have hz : CharZero W := charZero_of_injective_ringHom hi
  obtain ⟨t', m, hS'⟩ : ∃ (t' : SAB H (Sp W)) (_ : SABMap t' t (spMap (algebraMap T.V W))),
      ∃ S : SplitExt (Sp (ResidueField W)), S.IsGt ((Over.pullback (spMap (residue W))).obj t'.G) := by
    obtain ⟨PP', cub, sym, adj, prim, m, -⟩ := sabPull Out.CubePf.cubePull (spMap (algebraMap T.V W)) t
    exact ⟨_, m, hS⟩
  obtain ⟨gam, hsq⟩ := exists_generic_square (algebraMap T.V W) hi
  have hp := polAt_of_sabMap m mK mx Xo.univ.proper Xo.univ.ample Xo.univ.ktriv (jK W) gam hsq
  obtain ⟨-, P, -⟩ := isOpen_and_uniformised W hc t' hp hS'
  exact ⟨{ V := W }, algebraMap T.V W, t', m, hi, RingHom.finite_algebraMap.2 hf, ⟨P⟩⟩

end Unif

open scoped BigOperators TensorProduct
open NumberField IsLocalRing Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs GlobalTheory.CharDepth

open Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds GlobalTheory.RowLaw

section Map

variable {O C : Type} [CommRing O] [CommRing C] (φ : O →+* C) {dd : ℕ}

end Map

end GlobalTheory.ChartCharacters
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsLiftPrincipallyPolarisedAbelianSquareZero
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbelianLift

private theorem exists_odd_prime_ne (p : ℕ) : ∃ n : ℕ, n.Prime ∧ Odd n ∧ n ≠ p := by
  by_cases h : p = 3
  · exact ⟨5, by norm_num, by decide, by omega⟩
  · exact ⟨3, by norm_num, by decide, fun e => h e.symm⟩

theorem exists_lift : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (T : Type) [CommRing T] [IsNoetherianRing T] (P₀ : Out.PolAV (Geo.Tor.Sp T)) (io : T →+* O) (P : Out.PolAV (Geo.Tor.Sp O)) (φ : P.A.left ⟶ P₀.A.left), Geo.Tor.IsGrpPullback P.A P₀.A (Geo.Tor.spMap io) φ → Geo.Tor.LBIso P.L (P₀.L.pull φ) → P.g = P₀.g → 1 ≤ P.g → ∀ (R' : Type) [CommRing R'] (π : R' →+* O), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∃ (G : Over (Spec (CommRingCat.of R'))) (_ : GrpObj G) (_ : IsCommMonObj G) (Q : LB (G ⊗ G).left) (ψ : P.A.left ⟶ G.left) (ψ₂ : (P.A ⊗ P.A).left ⟶ (G ⊗ G).left), IsAbelianScheme G ∧ Q.IsLB ∧ (∃ t : (Q.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, t.IsGen) ∧ (∃ t : (Q.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, t.IsGen) ∧ Geo.Tor.LBIso Q (Q.pull (lift (snd G G) (fst G G)).left) ∧ Out.RelAmple G (Q.pull (lift (𝟙 G) (𝟙 G)).left) ∧ (∀ (Z : Over (Spec (CommRingCat.of R'))) (x : Z ⟶ G), (∃ t : (Q.pull (lift (snd G Z ≫ x) (fst G Z)).left).Gen, t.IsGen) → x = 1) ∧ Geo.Tor.IsGrpPullback P.A G (Spec.map (CommRingCat.ofHom π)) ψ ∧ Geo.Tor.IsSquare ψ ψ₂ ∧ Geo.Tor.LBIso (abelian₂ P.A P.L) (Q.pull ψ₂) := by
  intro p _ C _ _ _ v O _ _ hv _ _ T _ _ P₀ io P φ hφ hL hg h1 R' _ π hπ hker
  have hp : p.Prime := Fact.out
  have hinj : Function.Injective (algebraMap O C) := hv.hom_inj
  have : IsDomain O := hinj.isDomain _
  have : IsLocalRing O := by
    have : ValuationRing O := ValuationRing.of_integers v hv
    infer_instance
  obtain ⟨n, hn, hodd, hnp⟩ := exists_odd_prime_ne p
  obtain ⟨j, hj⟩ := GlobalTheory.ZM.SiegelLargeLevel.exists_siegelFamily_sRep GlobalTheory.firstFiveLaws.1 GlobalTheory.firstFiveLaws.2.1
    GlobalTheory.AbLaw.CubeAssembly.cube_gen GlobalTheory.thetaUnifAV_all P.g n h1 hn hodd
  obtain ⟨Ag, hAg⟩ := hj j le_rfl p hp hnp
  have hM0 : (n ^ j) ^ 2 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hn.ne_zero)
  have hcop : ((n ^ j) ^ 2).Coprime p :=
    Nat.Coprime.pow_left _ (Nat.Coprime.pow_left _ ((Nat.coprime_primes hn hp).2 hnp))
  generalize (n ^ j) ^ 2 = M at Ag hAg hM0 hcop
  obtain ⟨β, hβ, hMu, hprim⟩ := GlobalTheory.exists_zp_ringHom_integers p C v O hv M hM0 hcop
  have hζ : β (Geo.Tor.zetaZP p M) ^ M = 1 := hinj (by
    rw [map_pow, map_one]; exact (hprim C (algebraMap O C)).pow_eq_one)
  let ze : Oˣ := (IsUnit.of_pow_eq_one hζ hM0).unit
  have hze : (ze : O) = β (Geo.Tor.zetaZP p M) := rfl
  obtain ⟨lev, hl₁, hl₂, hl₃⟩ := GlobalTheory.exists_level_over_integers p C v O hv T P₀ io P φ hφ hL hg P.g M ze rfl hMu
    (hprim C (algebraMap O C))
  obtain ⟨c, e, he, hc, hcP⟩ := GlobalTheory.SiegelOverLocal.exists_siegPre O T P₀ io P φ hφ hL hg _ β P.g M (Geo.Tor.zetaZP p M) ze lev rfl hMu hze
    hprim hl₁ hl₂ hl₃
  obtain ⟨β', c', hc', φ₁, φ₂, hpb, hsq, hiso, -⟩ :=
    GlobalTheory.SiegelLift.exists_principal_lift P.g p M Ag hAg hcop hM0 O R' π hπ hker β hβ c hc
  let k : P.A ⊗ P.A ⟶ c.A ⊗ c.A := lift (fst P.A P.A ≫ e.inv) (snd P.A P.A ≫ e.inv)
  have hk : k.left ≫ (lift (fst c.A c.A ≫ e.hom) (snd c.A c.A ≫ e.hom)).left = 𝟙 _ := by
    rw [← Over.comp_left, ← Over.id_left]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp [k]
  have : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
  refine ⟨c'.A, c'.grp, c'.comm, c'.P, e.inv.left ≫ φ₁, k.left ≫ φ₂, c'.ab, c'.isLB, c'.rig₁, c'.rig₂, c'.symm,
    hc'.1, hc'.2, ?_, ⟨?_, ?_⟩, ?_⟩
  · exact ((Geo.Tor.isGrpPullback_of_iso e.symm).comp hpb).congr (Category.id_comp _) rfl
  · rw [Category.assoc, hsq.1, ← Category.assoc, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_fst]
  · rw [Category.assoc, hsq.2, ← Category.assoc, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_snd]
  · have hA : Geo.Tor.LBIso (abelian₂ P.A P.L) (c.P.pull k.left) :=
      Geo.Tor.LBIso.chartPull (Geo.Tor.chartPullSec _ _ k.left hk) (Geo.Tor.chartPullPull c.P k.left k.left rfl)
        hcP.symm
    have hB : Geo.Tor.LBIso (c.P.pull k.left) (c'.P.pull (k.left ≫ φ₂)) :=
      Geo.Tor.LBIso.chartPull (Geo.Tor.chartPullPull c.P k.left k.left rfl)
        (Geo.Tor.chartPullSame c'.P _ (fun _ => φ₂) _ k.left fun _ => rfl) hiso
    exact Geo.Tor.LBIso.trans (DVR.linComb_isLB _ P.isLB _ _) (DVR.linComb_isLB _ c.isLB _ _)
      (DVR.linComb_isLB _ c'.isLB _ _) hA hB

end GlobalTheory.AbelianLift
end

