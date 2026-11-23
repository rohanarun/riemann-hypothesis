module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0389
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0269
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieConditionOfBasicOpenCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2753
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2754
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2759
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0310
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1433
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0491
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0377
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0390
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0404
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryArchimedeanCoordinateActionSymplectic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0398
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0901
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0933
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0930
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0971
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0937
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0966
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0592
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2466
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2755
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2728
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2758
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieOcExistsSpMap
section
noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {S : Scheme.{0}}

theorem lieOc_spMap_inj {R₁ R₂ : Type} [CommRing R₁] [CommRing R₂] {f g : R₁ →+* R₂} (h : spMap f = spMap g) : f = g := by
  have := Spec.map_injective h
  exact congrArg CommRingCat.Hom.hom this

theorem lieOc_exists_spMap {R₁ R₂ : Type} [CommRing R₁] [CommRing R₂] (y : Sp R₂ ⟶ Sp R₁) : ∃ f : R₁ →+* R₂, y = spMap f :=
  ⟨(Spec.preimage y).hom, by simp [spMap]⟩

theorem lieOc_spMap_comp {R₁ R₂ R₃ : Type} [CommRing R₁] [CommRing R₂] [CommRing R₃] (f : R₁ →+* R₂) (g : R₂ →+* R₃) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp [spMap, ← Spec.map_comp]

theorem lieHer_closed (b : Base D R) (s : S ⟶ Sp R) (A : Over S) [GrpObj A] [IsCommMonObj A]
    (hA : Smooth A.hom) (act : OActN D.O A) :
    ∃ (Z : Scheme.{0}) (i : Z ⟶ S), IsClosedImmersion i ∧
      ∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ S), x ≫ s = spMap β →
        ((∃ y : Sp R' ⟶ Z, y ≫ i = x) ↔ LieHer b act β x) := by
  let P : ∀ (R' : Type) [CommRing R'], (Sp R' ⟶ S) → Prop := fun R' _ x =>
    ∀ β : R →+* R', x ≫ s = spMap β → LieHer b act β x
  have hP : ∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ S), x ≫ s = spMap β →
      (P R' x ↔ LieHer b act β x) := by
    intro R' _ β x hx
    refine ⟨fun h => h β hx, fun h β' hx' => ?_⟩
    have : β' = β := lieOc_spMap_inj (hx'.symm.trans hx)
    subst this; exact h

  have her : ∀ (R' : Type) [CommRing R'] (R'' : Type) [CommRing R''] (g : R' →+* R'') (x : Sp R' ⟶ S),
      P R' x → P R'' (spMap g ≫ x) := by
    intro R' _ R'' _ g x hx β'' hβ''
    obtain ⟨β, hβ⟩ := lieOc_exists_spMap (x ≫ s)
    have e : β'' = g.comp β := lieOc_spMap_inj (by rw [← hβ'', Category.assoc, hβ, lieOc_spMap_comp])
    subst e
    intro R''' _ g'
    have h := hx β hβ R''' (g'.comp g)
    rw [← lieOc_spMap_comp] at h
    simpa [Category.assoc, RingHom.comp_assoc] using h

  have loc : ∀ (R' : Type) [CommRing R'] (x : Sp R' ⟶ S) (t : Finset R'), Ideal.span (t : Set R') = ⊤ →
      (∀ r ∈ t, P (Localization.Away r) (spMap (algebraMap R' (Localization.Away r)) ≫ x)) → P R' x := by
    classical
    intro R' _ x t ht hloc β hβ R'' _ g
    have hloc' : ∀ r ∈ t, LieHer b act ((algebraMap R' (Localization.Away r)).comp β)
        (spMap (algebraMap R' (Localization.Away r)) ≫ x) := fun r hr =>
      hloc r hr _ (by rw [Category.assoc, hβ, lieOc_spMap_comp])
    have key : ∀ r : R', (Localization.awayMap g r).comp (algebraMap R' (Localization.Away r)) =
        (algebraMap R'' (Localization.Away (g r))).comp g := fun r => IsLocalization.map_comp _
    refine ⟨?_, ?_⟩
    · refine _root_.GlobalTheory.UPel.HT.LieLoc.lieAt_of_cover p D R b S A act R'' (g.comp β) (spMap g ≫ x) (t.image g) ?_ ?_
      · rw [Finset.coe_image, ← Ideal.map_span, ht, Ideal.map_top]
      · intro r'' hr''
        obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hr''
        have h := (hloc' r hr (Localization.Away (g r)) (Localization.awayMap g r)).1
        rw [← Category.assoc, lieOc_spMap_comp, ← RingHom.comp_assoc, key] at h
        rw [← Category.assoc, lieOc_spMap_comp, ← RingHom.comp_assoc]
        exact h
    · intro k _ _ g' i
      have hex : ∃ r ∈ t, g' (g r) ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        have : Ideal.span (t : Set R') ≤ RingHom.ker (g'.comp g) :=
          Ideal.span_le.2 fun r hr => by simpa using hcon r hr
        rw [ht] at this
        have h1 : (1 : R') ∈ RingHom.ker (g'.comp g) := this Submodule.mem_top
        simp at h1
      obtain ⟨r, hr, hne⟩ := hex
      let hr' : Localization.Away r →+* k := IsLocalization.Away.lift r (g := g'.comp g) (isUnit_iff_ne_zero.2 hne)
      have hlift : hr'.comp (algebraMap R' (Localization.Away r)) = g'.comp g :=
        IsLocalization.Away.lift_comp r _
      have h := (hloc' r hr (Localization.Away r) (RingHom.id _)).2 k hr' i
      have e1 : spMap hr' ≫ spMap (RingHom.id (Localization.Away r)) ≫ spMap (algebraMap R' (Localization.Away r)) ≫ x =
          spMap g' ≫ spMap g ≫ x := by
        simp only [← Category.assoc, lieOc_spMap_comp]
        rw [RingHom.id_comp, hlift]
      have e2 : hr'.comp ((RingHom.id _).comp ((algebraMap R' (Localization.Away r)).comp β)) = g'.comp (g.comp β) := by
        rw [RingHom.id_comp, ← RingHom.comp_assoc, hlift, RingHom.comp_assoc]
      rw [e1, e2] at h
      exact h
  obtain ⟨Z, i, hi, hZ⟩ := _root_.GlobalTheory.PtClosed.closed_of_points S P her loc (fun z => by
    obtain ⟨U, hU, hz, K, hK⟩ := GlobalTheory.T.kottwitzLieCondition_locally_cut_out_by_ideal p D R b S s A hA act z
    refine ⟨U, hU, hz, K, fun R' _ f => ?_⟩
    obtain ⟨β, hβ⟩ := lieOc_exists_spMap (spMap f ≫ hU.fromSpec ≫ s)
    rw [hP R' β _ (by rw [Category.assoc]; exact hβ)]
    exact hK R' f β hβ)
  exact ⟨Z, i, hi, fun R' _ β x hx => (hZ R' x).trans (hP R' β x hx)⟩

end GlobalTheory.UPel.HT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTrivialityOfNoetherianDescentStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localTriviality_of_noetherian_descent : (∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (M : LB A.left), M.IsLB → (∃ t : (M.pull (1 : 𝟙_ (Over (Sp R)) ⟶ A).left).Gen, t.IsGen) → ∀ k : ℕ, IsUnit (k : R) → (∃ t : (GlobalTheory.UPel.HT.Hecke.lbPow M k).Gen, t.IsGen) → ∀ (K : Type) [Field K] (g₀ : R →+* K), (∃ t : (M.pull (pullback.fst A.hom (spMap g₀))).Gen, t.IsGen) → ∃ r : R, g₀ r ≠ 0 ∧ ∃ t : (M.pull (A.hom ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι).Gen, t.IsGen) → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (M : LB A.left), M.IsLB → (∃ t : (M.pull (1 : 𝟙_ (Over (Sp R)) ⟶ A).left).Gen, t.IsGen) → ∀ k : ℕ, IsUnit (k : R) → (∃ t : (GlobalTheory.UPel.HT.Hecke.lbPow M k).Gen, t.IsGen) → ∀ (K : Type) [Field K] (g₀ : R →+* K), (∃ t : (M.pull (pullback.fst A.hom (spMap g₀))).Gen, t.IsGen) → ∃ r : R, g₀ r ≠ 0 ∧ ∃ t : (M.pull (A.hom ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι).Gen, t.IsGen := by
  first | (exact @GlobalTheory.LocTrivDescent.locTriv_of_noetherian) | (exact GlobalTheory.LocTrivDescent.locTriv_of_noetherian) | (intros; apply GlobalTheory.LocTrivDescent.locTriv_of_noetherian <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleGlobalLiftIdentity
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open MeasureTheory Filter Topology
open scoped Classical

noncomputable section

namespace GlobalTheory.ThetaIntegralLine

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {Y : Spc F E n} {W : Spc F E d}

theorem I_om_one (M : Model σ Y W) (om : Rep σ Y W) (Φ : Fn F n d) (k h : UA σ W.J) :
    M.I om (om (1, k) Φ) h = M.I om Φ (h * k) := by
  unfold Model.I theta
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  show thetaSum F (om (g, h) (om (1, k) Φ)) = thetaSum F (om (g, h * k) Φ)
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

theorem I_smul (M : Model σ Y W) (om : Rep σ Y W) (c : ℂ) (Φ : Fn F n d) (h : UA σ W.J) :
    M.I om (c • Φ) h = c * M.I om Φ h := by
  unfold Model.I theta
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  show thetaSum F (om (g, h) (c • Φ)) = c * thetaSum F (om (g, h) Φ)
  rw [map_smul, thetaSum_smul]

theorem I_add (M : Model σ Y W) (om : Rep σ Y W) (hpres : ∀ x, ∀ Φ ∈ schA F (Fin n × Fin d), om x Φ ∈ schA F (Fin n × Fin d))
    (hconv : ∀ Φ ∈ schA F (Fin n × Fin d), M.Conv om Φ) {Φ Ψ : Fn F n d} (hΦ : Φ ∈ schA F (Fin n × Fin d))
    (hΨ : Ψ ∈ schA F (Fin n × Fin d)) (h : UA σ W.J) : M.I om (Φ + Ψ) h = M.I om Φ h + M.I om Ψ h := by
  unfold Model.I
  rw [← integral_add (hconv Φ hΦ h) (hconv Ψ hΨ h)]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  show thetaSum F (om (g, h) (Φ + Ψ)) = thetaSum F (om (g, h) Φ) + thetaSum F (om (g, h) Ψ)
  rw [map_add (f := _), thetaSum_add F (hpres _ _ hΦ) (hpres _ _ hΨ)]

theorem snd_eq_zero_of_at {κ : Type} (z : κ → AF F) (hz : At (evI F) z) (i : κ) : (z i).2 = 0 := by
  let u : AF F := (show InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F from (0, 1))
  have hu : evI F u = 0 := by
    show (InfiniteAdeleRing.ringEquiv_mixedSpace F) (0 : InfiniteAdeleRing F) = 0
    exact map_zero _
  have h1 : (1 : FiniteAdeleRing (𝓞 F) F) * (z i).2 = 0 := congrArg Prod.snd (congrFun (hz u hu) i)
  rwa [one_mul] at h1

end GlobalTheory.ThetaIntegralLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinpolyOfRegAfOfFixL
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical ComplexOrder

theorem GlobalTheory.LKCx.minpoly_of_regAf_of_fixL : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F), sigPosH (G.gram_herm v) = 1 → ∀ (β : G.Cˣ), sh G β = β → (∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) → ∀ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t) (y : grp G β) (h : G.GAf) (z : PosV G v β), FixL G v β y z.1 → RegAf G (h⁻¹ * toAfF G β x t hx y * h) → (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n ∧ (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable := by
  intro p _ G v hv β hβ hR x t hx y h z hfix hreg
  have hcomm : ∀ a b : G.C, Commute a (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) →
      Commute b (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) → Commute a b := by
    obtain ⟨w, hw⟩ := hreg
    obtain ⟨U, hU⟩ := ubc_val_eq G β x t hx y h w
    rw [hU] at hw
    intro a b ha hb
    let ι : G.C →ₐ[ℚ] w.1.adicCompletion ℚ ⊗[ℚ] G.C := Algebra.TensorProduct.includeRight
    have hinj : Function.Injective ι :=
      Algebra.TensorProduct.includeRight_injective (algebraMap ℚ (w.1.adicCompletion ℚ)).injective
    have e : ι (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) =
        (1 : w.1.adicCompletion ℚ) ⊗ₜ (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) := rfl
    have ha' := ha.map ι
    have hb' := hb.map ι
    rw [e] at ha' hb'
    have hab := comm_of_conj U _ hw (ι a) (ι b) ha' hb'
    exact hinj (by rw [map_mul, map_mul]; exact hab.eq)
  obtain ⟨-, -, Z, hZ⟩ := GlobalTheory.LKCx.herm_laws p G v β hβ hR
  have hsim := GlobalTheory.LKCx.grp_similitude_herm p G v β y
  have hs : (0 : ℝ) < ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) := by exact_mod_cast y.2.2
  obtain ⟨c0, hc0⟩ := hfix
  obtain ⟨H, hH, hHM⟩ := GlobalTheory.T.similitude_signature_one_preserves_posDef_form G.n (G.gram v) (herm G v β) (toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ)
    (G.gram_herm v) Z _ (G.gram_det v) hv hZ hs (by rw [Complex.ofReal_ratCast]; exact hsim) z.1 c0 z.2 hc0
  have hsq := GlobalTheory.T.aeval_eq_zero_of_sq_eq_zero_of_posDef_similitude G.n H _ _ hH hs hHM
  have hsep := GlobalTheory.T.minpoly_separable_of_no_sq_zero_polynomial_image G.F G.C G.n v.embedding (G.psi v) G.n_pos (G.psi_F v) _ hsq
  exact ⟨GlobalTheory.T.natDegree_minpoly_eq_deg_centralSimple_commCentraliser G.F G.C G.n G.rankC _ hsep hcomm, hsep⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedSeesawTriplePrimeThetaIntegralEqScaled
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotMove

namespace GlobalTheory.BotMove

open MeasureTheory

theorem int_prime_moveTri : ∀ {D : D7} {T : Type} {A A' WW : HSp D} (Y : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (α β : T → ((AE D)ˣ →* Circle)) (νH : T → HChar D.host.E) (S : T → Finset (Formalism.L2.DIV.Pl D.host.E)),
    Y.Is ψ θ α β νH S →
    ∀ (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (ΛA' : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E))
      (ΛW : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)),
    ∀ (g : GA D A), ∀ g' ∈ GfC A', ∀ h ∈ GfC WW, ∀ (t₀ : T) (r r' : T → ℂ), (∀ t, r' t ≠ 0) →
    ∀ t P (y : GA D WW),
      (MeasureTheory.IntegrableOn ((moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').ker' ψ θ t P y) (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').fd'
          (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').m' ↔ MeasureTheory.IntegrableOn (Y.ker' ψ θ t P (y * h)) Y.fd' Y.m') ∧
      (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').I' ψ θ t P y = (r' t)⁻¹ * Y.I' ψ θ t P (y * h) := by
  intro D T A A' WW Y ψ θ α β νH S hY ΛA ΛA' ΛW g g' hg' h hh t₀ r r' hr' t P y
  have hW : IsWeilDatumO ψ A' WW (α t) (α t / β t) (Y.ω' t) := hY.weil' t
  have hθ : IsInfFam θ := hY.isVac'.2.inf
  have hf := (GlobalTheory.ConstRatio.theta_f hY t).2
  have hk : ∀ x, (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').ker' ψ θ t P y x = (r' t)⁻¹ * Y.ker' ψ θ t P (y * h) (x * g') := by
    intro x
    change thetaKO (Y.ω' t) x y (pureTensorO ψ θ A' WW Y.rA'.s Y.rW.s Y.rA'.B Y.rW.B
      ((r' t)⁻¹ • Y.ω' t (g', h) (Y.f' t)) P) = (r' t)⁻¹ * thetaKO (Y.ω' t) (x * g') (y * h)
        (pureTensorO ψ θ A' WW Y.rA'.s Y.rW.s Y.rA'.B Y.rW.B (Y.f' t) P)
    rw [GlobalTheory.FiniteFock.pureTensorO_smul, ← (GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ A' WW _ _ (Y.ω' t) hW hθ
      Y.rA'.s Y.rA'.s Y.rA'.B Y.rA'.B Y.rW.s Y.rW.s Y.rW.B Y.rW.B g' h
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hg', Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hh, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hg', Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hh, Matrix.one_mul]) _ hf P).2]
    simp only [thetaKO, map_smul, Pi.smul_apply, smul_eq_mul]
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk]
  let e : GA D A' ≃ᵐ GA D A' := MeasurableEquiv.mulRight g'⁻¹
  have hm : (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').m' = Y.m'.map e := rfl
  have hs : e ⁻¹' (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').fd' = Y.fd' := by
    ext x
    change x * g'⁻¹ * g' ∈ Y.fd' ↔ x ∈ Y.fd'
    rw [inv_mul_cancel_right]
  have hc : ∀ x, (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').ker' ψ θ t P y (e x) = (r' t)⁻¹ * Y.ker' ψ θ t P (y * h) x := by
    intro x
    rw [hk]
    change (r' t)⁻¹ * Y.ker' ψ θ t P (y * h) (x * g'⁻¹ * g') = _
    rw [inv_mul_cancel_right]
  have hu : IsUnit (r' t)⁻¹ := IsUnit.mk0 _ (inv_ne_zero (hr' t))
  constructor
  · rw [hm, integrableOn_map_equiv, hs]
    change Integrable (fun x => (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').ker' ψ θ t P y (e x)) (Y.m'.restrict Y.fd') ↔ _
    simp_rw [hc]
    exact integrable_const_mul_iff hu _
  · change ∫ x in (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').fd', (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').ker' ψ θ t P y x
        ∂(moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').m' = (r' t)⁻¹ * ∫ x in Y.fd', Y.ker' ψ θ t P (y * h) x ∂Y.m'
    rw [hm, setIntegral_map_equiv, hs]
    simp_rw [hc]
    exact integral_const_mul _ _

end GlobalTheory.BotMove
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedSeesawTripleThetaIntegralEqScaled
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotMove

noncomputable section

open MeasureTheory GlobalTheory.Grid

namespace GlobalTheory.BotMove

variable {D : D7} {T : Type} {A A' WW : HSp D}

theorem moveTri_ker (Y : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    {α β : T → ((AE D)ˣ →* Circle)} {νH : T → HChar D.host.E} {S : T → Finset (Formalism.L2.DIV.Pl D.host.E)}
    (hY : Y.Is ψ θ α β νH S) (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E))
    (ΛA' : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E))
    {g : GA D A} (hg : g ∈ GfC A) (g' : GA D A') {h : GA D WW} (hh : h ∈ GfC WW) (t₀ : T) (r r' : T → ℂ)
    (t : T) (P : PolF D WW.rank A.rank) (y : GA D WW) (x : GA D A) :
    (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').ker ψ θ t P y x = (r t)⁻¹ * Y.ker ψ θ t P (y * h) (x * g) := by
  have hgs : (ofSgn true A).symm g ∈ GfC (neg A) := hg
  have key : Y.ω t (g, h) (pureTensorO ψ θ (neg A) WW (fun τ => -Y.rA.s τ) Y.rW.s Y.rA.B Y.rW.B (Y.f t) P) =
      pureTensorO ψ θ (neg A) WW (fun τ => -Y.rA.s τ) Y.rW.s Y.rA.B Y.rW.B (Y.ω t (g, h) (Y.f t)) P :=
    (GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ (neg A) WW _ _ ((Y.ω t).toSgn true) (hY.weil t) hY.isVac.2.inf
      (fun τ => -Y.rA.s τ) (fun τ => -Y.rA.s τ) Y.rA.B Y.rA.B Y.rW.s Y.rW.s Y.rW.B Y.rW.B ((ofSgn true A).symm g) h
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hgs, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hh, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hgs, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hh, Matrix.one_mul])
      (Y.f t) (GlobalTheory.ConstRatio.theta_f hY t).1 P).2
  show Y.ω t (x, y) (pureTensorO ψ θ (neg A) WW (fun τ => -Y.rA.s τ) Y.rW.s Y.rA.B Y.rW.B
      ((r t)⁻¹ • Y.ω t (g, h) (Y.f t)) P) 0 =
    (r t)⁻¹ * Y.ω t (x * g, y * h) (pureTensorO ψ θ (neg A) WW (fun τ => -Y.rA.s τ) Y.rW.s Y.rA.B Y.rW.B (Y.f t) P) 0
  rw [GlobalTheory.FiniteFock.pureTensorO_smul, map_smul, Pi.smul_apply, smul_eq_mul, ← key, ← Module.End.mul_apply, ← map_mul]
  rfl

theorem moveTri_I : ∀ {D : D7} {T : Type} {A A' WW : HSp D} (Y : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (α β : T → ((AE D)ˣ →* Circle)) (νH : T → HChar D.host.E) (S : T → Finset (Formalism.L2.DIV.Pl D.host.E)),
    Y.Is ψ θ α β νH S →
    ∀ (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (ΛA' : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E))
      (ΛW : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)),
    ∀ g ∈ GfC A, ∀ (g' : GA D A'), ∀ h ∈ GfC WW, ∀ (t₀ : T) (r r' : T → ℂ), (∀ t, r t ≠ 0) →
    ∀ t P (y : GA D WW),
      (MeasureTheory.IntegrableOn ((moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').ker ψ θ t P y) (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').fd
          (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').m ↔ MeasureTheory.IntegrableOn (Y.ker ψ θ t P (y * h)) Y.fd Y.m) ∧
      (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').I ψ θ t P y = (r t)⁻¹ * Y.I ψ θ t P (y * h) := by
  intro D T A A' WW Y ψ θ α β νH S hY ΛA ΛA' ΛW g hg g' h hh t₀ r r' hr t P y
  have hk : (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').ker ψ θ t P y = fun x => (r t)⁻¹ * Y.ker ψ θ t P (y * h) (x * g) :=
    funext (moveTri_ker Y ψ θ hY ΛA ΛA' ΛW hg g' hh t₀ r r' t P y)
  have he : MeasurableEmbedding (fun x : GA D A => x * g⁻¹) := (MeasurableEquiv.mulRight g⁻¹).measurableEmbedding
  have hpre : (fun x : GA D A => x * g⁻¹) ⁻¹' ((fun x => x * g) ⁻¹' Y.fd) = Y.fd := by
    ext x; simp
  have hu : IsUnit (r t)⁻¹ := isUnit_iff_ne_zero.2 (inv_ne_zero (hr t))
  constructor
  · show IntegrableOn ((moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').ker ψ θ t P y) ((fun x => x * g) ⁻¹' Y.fd)
      (Y.m.map fun x => x * g⁻¹) ↔ _
    rw [he.integrableOn_map_iff, hpre, hk]
    simp only [Function.comp_def, inv_mul_cancel_right]
    exact integrable_const_mul_iff hu _
  · show ∫ x in (fun x => x * g) ⁻¹' Y.fd, (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').ker ψ θ t P y x ∂(Y.m.map fun x => x * g⁻¹) =
      (r t)⁻¹ * ∫ x in Y.fd, Y.ker ψ θ t P (y * h) x ∂Y.m
    rw [he.setIntegral_map, hpre, hk]
    simp only [inv_mul_cancel_right]
    exact integral_const_mul _ _

end GlobalTheory.BotMove

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplierPowerMulPullbackSmallFamilyStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplier_power_mul_pullback_small_family : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G), ∀ b, FormalEnd U.toUnifPre a h' b → ∀ (N k : ℕ) (g : ∀ β, SecT D.toPre a N (-1) β) (ρ : ∀ β, SecT D.toPre a 0 k β), Small (maximalIdeal R) (w := id) g → Small (maximalIdeal R) (w := id) ρ → TFE h h' g → TFE h h' ρ → ∃ F : ∀ β, SecT D.toPre a ((N * k : ℕ) : ℤ) 0 β, Small (maximalIdeal R) (w := id) F ∧ TFE h h' F ∧ ∀ (e : ℕ) (τ : SecE U.toUnifPre (b e) N (-1)) (τ' : SecE U.toUnifPre (b e) 0 k), TExp U.toUnifPre τ (w := id) g → TExp U.toUnifPre τ' (w := id) ρ → ∃ τ'' : SecE U.toUnifPre (b e) ((N * k : ℕ) : ℤ) 0, (∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J'), Good U.LG.L z J' → sval τ'' x z J' = sval τ x z J' ^ k * sval τ' x z J') ∧ TExp U.toUnifPre τ'' (w := id) F := by
  first | exact @GlobalTheory.ZmPow.pow_mul_small | exact GlobalTheory.ZmPow.pow_mul_small | (intros; apply GlobalTheory.ZmPow.pow_mul_small <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneSquareFittedIdentity
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField
open Formalism.L2.Indef.Tree

namespace GlobalTheory.BigTop.Fun.OneSqTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem big_std : GlobalTheory.RowClaim.Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => Formalism.L2.Theta.IsStdChar D ch.W.ψ (-1) :=
  ⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s _ hi _ => by
    show Formalism.L2.Theta.IsStdChar _ _ (-1)
    rw [hi.weil.ψ]; exact s.std⟩⟩

end GlobalTheory.BigTop.Fun.OneSqTie

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupIsogenyHeightEqDualSameDegreeStatement
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pDivGroupIsogeny_height_eq_dual_sameDegree : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (G H : PDivGroup p k) (q : G ⟶ H), IsIsog q → G.height = H.height ∧ IsIsog (dualHom G H q) ∧ ∀ e, HasLogDeg q e → HasLogDeg (dualHom G H q) e := by
  first | exact @GlobalTheory.Dieu.height_eq_and_dual_isog | exact GlobalTheory.Dieu.height_eq_and_dual_isog | (intros; apply GlobalTheory.Dieu.height_eq_and_dual_isog <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDegenerationDataTorsionIsometryOntoStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorDegenerationData_torsion_isometry_onto : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det → ∀ T : Tens D.toPre D'.toPre W, ∀ (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ), (∀ a, (ρ a).transpose * (W + W.transpose) = (W + W.transpose) * ρ (H.bar a)) → W = (W + W.transpose) * ρ H.w0 → ∀ [Module (𝓞 E) D'.toPre.X] (o : letI := H.starRing; D'.toPre.OAct (𝓞 E)), (letI := H.starRing; T.IsAct o ρ) → (letI := H.starRing; TraceFormTwistIso D'.toPre o H.w0) → ∀ (Dm : Datum H) (g : ℕ) (e : Dm.La ≃+ (Fin r → (Fin g → ℤ) × (Fin g → ℤ))), g = D.toPre.P.g + Module.finrank ℤ D.toPre.X → (∀ (a : 𝓞 E) x i, e (a • x) i = ∑ j, ρ a i j • e x j) → (∀ x y, Dm.EF x y = ∑ i, ∑ j, (W + W.transpose) i j * ((e x i).1 ⬝ᵥ (e y j).2 - (e x i).2 ⬝ᵥ (e y j).1)) → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (ζ : ℕ → Fˣ), (∀ n, 0 < n → IsPrimitiveRoot (ζ n) n) → (∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n) → ∀ ev : ∀ n : ℕ, ((Fin g → ℤ) × (Fin g → ℤ)) → QkPt D.toPre F n, (∀ n, 0 < n → ∀ a b, QkAdd (ev n a) (ev n b) (ev n (a + b))) → (∀ n, 0 < n → ∀ a b, QkPt.Equiv D.toPre F (ev n a) (ev n b) ↔ ∃ e, a = b + n • e) → (∀ n, 0 < n → ∀ p, ∃ a, QkPt.Equiv D.toPre F (ev n a) p) → (∀ n m, 0 < n → 0 < m → ∀ a, ∃ q : QkPt D.toPre F n, q.y = (ev (n * m) a).y ∧ GtPtF.IsNsmul m (ev (n * m) a).g q.g ∧ QkPt.Equiv D.toPre F q (ev n a)) → (∀ n, 0 < n → ∀ a b, WeilQkIs D.toPre F n (ev n a) (ev n b) ((ζ n ^ (a.1 ⬝ᵥ b.2 - a.2 ⬝ᵥ b.1) : Fˣ) : F)) → ∃ I : TateIsoQ Dm D'.toPre o F, I.ζ = ζ := by
  first | exact @GlobalTheory.Mum.TensTor.tate_tens | exact GlobalTheory.Mum.TensTor.tate_tens | (intros; apply GlobalTheory.Mum.TensTor.tate_tens <;> assumption)
end

