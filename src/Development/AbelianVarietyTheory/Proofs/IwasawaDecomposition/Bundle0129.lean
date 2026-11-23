module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0122
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExtUHInjective
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0124
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PowEqPowIffModEqOfIsPrimitiveRoot
public import Formalism.LocalToGlobal.Columns.HeckeInertComm
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.LatticeBasisExistsHolds
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryLastRowDivisibleStabilizesLattices
public import Formalism.LocalToGlobal.Columns.RecLevelLocK

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PhiDeXExpand
section
open MvPolynomial

noncomputable section
namespace GlobalTheory.WeylLatDualProof

theorem minY_colsOf_eq (p : ℕ) [Fact p.Prime] {Lt T : Type} [Fintype Lt] (e : Lt → T) (N : ℕ)
    (nu : Lt → YoungDiagram) (hY : ∀ s, (nu s).colLen 0 ≤ N) (y : T → Matrix (Fin N) (Fin N) ℂ_[p])
    (J : ∀ s, IncreasingRowChoicePerColumn N (nu s)) :
    PI.WwCauchyBinet.minY N nu J (fun s => WeylLatticeDuality.colsOf (y (e s))) =
      ∏ s, MvPolynomial.eval (fun k : Fin N × Fin N => y (e s) k.1 k.2)
        (MvPolynomial.map (algebraMap ℚ ℂ_[p]) (GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) (J s))) := by
  unfold PI.WwCauchyBinet.minY GlobalTheory.WeylMinorDual.colProd Formalism.GradedWeylDivisibility.bideterminant
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  unfold Formalism.GradedWeylDivisibility.initMinor
  rw [RingHom.map_det, RingHom.map_det]
  congr 1
  ext i j
  have hj : (j : ℕ) < N := lt_of_lt_of_le j.2 (GlobalTheory.WeylMinorDual.colLen_le (hY s) c)
  simp [WeylLatticeDuality.colsOf, hj, Fin.castLE]

theorem map_nablaX_expand (p : ℕ) [Fact p.Prime] {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N : ℕ)
    (nu : Lt → YoungDiagram) (hY : ∀ s, (nu s).colLen 0 ≤ N) (ι : Lt → Type) [∀ s, Fintype (ι s)]
    (b : ∀ s, ι s → MvPolynomial (Fin N × Fin N) ℚ) (c : ∀ s, IncreasingRowChoicePerColumn N (nu s) → ι s → ℤ)
    (hb : ∀ s J, GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J = ∑ k, (c s J k : ℚ) • b s k)
    (J : ∀ s, IncreasingRowChoicePerColumn N (nu s)) :
    MvPolynomial.map (Int.castRingHom ℂ_[p]) (WeylLatticeDuality.nablaX N nu J) =
      ∑ κ : (∀ s, ι s), (∏ s, ((c s (J s) (κ s) : ℤ) : ℂ_[p])) •
        MvPolynomial.map (algebraMap ℚ ℂ_[p]) (∏ s, MvPolynomial.rename (sig N s) (b s (κ s))) := by
  have h0 : (Int.castRingHom ℂ_[p]) = (algebraMap ℚ ℂ_[p]).comp (Int.castRingHom ℚ) := RingHom.ext_int _ _
  rw [h0, ← MvPolynomial.map_map, map_nablaX ℚ N nu hY J]
  set_option synthInstance.maxHeartbeats 100000 in
    simp_rw [hb, map_sum, map_smul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Fintype.prod_sum, map_sum]
  refine Finset.sum_congr rfl fun κ _ => ?_
  simp only [smul_eq_C_mul, Finset.prod_mul_distrib, map_mul, map_prod, MvPolynomial.map_C]
  congr 1
  refine Finset.prod_congr rfl fun s _ => ?_
  simp

theorem phi_DeX_expand : ∀ (p : ℕ) [Fact p.Prime] (Lt T : Type) [Fintype Lt] [DecidableEq Lt] [Fintype T] (e : Lt → T) (N : ℕ)
    (nu : Lt → YoungDiagram) (hY : ∀ s, (nu s).colLen 0 ≤ N) (ι : Lt → Type) [∀ s, Fintype (ι s)]
    (b g : ∀ s, ι s → MvPolynomial (Fin N × Fin N) ℚ) (c : ∀ s, GlobalTheory.WeylLatDualProof.IncreasingRowChoicePerColumn N (nu s) → ι s → ℤ),
    (∀ s J, GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J = ∑ k, (c s J k : ℚ) • b s k) →
    (∀ s k, g s k = ∑ J, (c s J k : ℚ) • GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J) →
    ∀ (φ : Module.Dual ℂ_[p] (MvPolynomial (Lt × ℕ × Fin N) ℂ_[p])) (y : T → Matrix (Fin N) (Fin N) ℂ_[p]),
      φ (WeylLatticeDuality.DeX N nu fun s => WeylLatticeDuality.colsOf (y (e s))) =
        ∑ κ : (∀ s, ι s), φ (MvPolynomial.map (algebraMap ℚ ℂ_[p])
            (∏ s, MvPolynomial.rename (GlobalTheory.WeylLatDualProof.sig N s) (b s (κ s)))) *
          ∏ s, MvPolynomial.eval (fun k : Fin N × Fin N => y (e s) k.1 k.2)
            (MvPolynomial.map (algebraMap ℚ ℂ_[p]) (g s (κ s))) := by
  intro p _ Lt T _ _ _ e N nu hY ι _ b g c hb hg φ y
  have h1 := cauchy_binet_minors Lt ℂ_[p] N nu (fun s => WeylLatticeDuality.colsOf (y (e s)))
  rw [finsum_eq_sum_of_fintype] at h1
  have h2 : WeylLatticeDuality.DeX N nu (fun s => WeylLatticeDuality.colsOf (y (e s))) =
      ∑ J : (∀ s, IncreasingRowChoicePerColumn N (nu s)), MvPolynomial.C (PI.WwCauchyBinet.minY N nu J
        (fun s => WeylLatticeDuality.colsOf (y (e s)))) *
        MvPolynomial.map (Int.castRingHom ℂ_[p]) (WeylLatticeDuality.nablaX N nu J) := by
    convert h1 using 2
    all_goals try rfl
  have hG : ∀ s k, MvPolynomial.eval (fun k : Fin N × Fin N => y (e s) k.1 k.2)
      (MvPolynomial.map (algebraMap ℚ ℂ_[p]) (g s k)) = ∑ J, ((c s J k : ℤ) : ℂ_[p]) *
        MvPolynomial.eval (fun k : Fin N × Fin N => y (e s) k.1 k.2)
          (MvPolynomial.map (algebraMap ℚ ℂ_[p]) (GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J)) := by
    intro s k
    rw [hg]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, smul_eq_C_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h2, map_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp_rw [MvPolynomial.C_mul', map_smul, map_nablaX_expand p N nu hY ι b c hb, minY_colsOf_eq p e N nu hY y,
    map_sum, map_smul, smul_eq_mul, hG, Fintype.prod_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun κ _ => Finset.sum_congr rfl fun J _ => ?_
  rw [Finset.prod_mul_distrib]
  ring

end GlobalTheory.WeylLatDualProof
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationSquaresAgreeAtEachThickeningStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarization_squares_agree_at_each_thickening : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I →
    ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R)))
    [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : UnifPre I D A G) (U' : UnifPre I D' A' G)
    (wL : LB.Iso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))
      (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), wL.IsGen →
    (∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over (Spec (CommRingCat.of R)))).left) (z : Z) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι),
      eSec G (r z) ∈ U.LG.L.U jL → eSec G (r z) ∈ U'.LG.L.U jL' →
      gm r z _ (U.LG.rig.s (fun _ => jL)) ^ 2 =
        gv wL (r ≫ eSec G) z (fun _ => jL) (fun _ => jL') * gm r z _ (U'.LG.rig.s (fun _ => jL')) ^ 2) →
    ∀ (e : ℕ) (β : thickObj R I e D'.toPre.P.A ≅ thickObj R I e D.toPre.P.A), IsMonHom β.hom →
    (U'.gt e).q ≫ β.hom = (U.gt e).q →
    ∃ v : LB.Iso ((LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)).pull
        (fstG I e D'.toPre.P.A).left)
      ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull
        (β.hom.left ≫ (fstG I e D.toPre.P.A).left)), v.IsGen ∧
    ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι)
      (jL : U.LG.L.ι) (jL' : U'.LG.L.ι),
      (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' →
      (fstG I e G).left (r z) ∈ U.LG.L.U jL → (fstG I e G).left (r z) ∈ U'.LG.L.U jL' →
      gw v (r ≫ (U'.gt e).q.left) z (fun _ => jM) (fun _ => fun _ => jM') * gw (U'.w e) r z jM' (fun _ => jL') ^ 2 =
        gw (U.w e) r z jM (fun _ => jL) ^ 2 * gv wL (r ≫ (fstG I e G).left) z (fun _ => jL) (fun _ => jL') := by
  first | exact @GlobalTheory.polarisation_squares_agree_at_level | exact GlobalTheory.polarisation_squares_agree_at_level | (intros; apply GlobalTheory.polarisation_squares_agree_at_level <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrimeNotMemOfMemQE
section
noncomputable section

namespace GlobalTheory.Mem.Col2

open NumberField IsDedekindDomain Formalism.BasicNotions _root_.Formalism.L2.Col Formalism.L2.DIV


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.Mem.Col2.T_notMem_QE : ∀ {X : _root_.Formalism.L2.Col.Fields} {Pr : _root_.Formalism.L2.Col.Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E))
    {S : Set ℕ} (mu : _root_.Formalism.L2.DIV.Tup X.F X.E X.K S) (u : Pr.Word), Pr.Ok → _root_.Formalism.L2.Col.IsSel X sel → Pr.T u ∈ S →
      ∀ w ∈ _root_.Formalism.L2.Col.QE sel (mu : _root_.Formalism.L2.DIV.Chr X.F X.E X.K), (Pr.T u : 𝓞 X.E) ∉ w.asIdeal := by
  classical
  intro X Pr sel S mu u hOk hsel hT w hw hmem
  unfold _root_.Formalism.L2.Col.QE at hw
  split_ifs at hw with hfin
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    rw [Set.Finite.mem_toFinset] at hv
    have hmu := mu.2
    unfold _root_.Formalism.L2.DIV.tupGrp at hmu
    simp only [Subgroup.mem_inf, Subgroup.mem_iInf] at hmu
    have hA : _root_.Formalism.L2.DIV.GoodPl X.E S v := by
      by_contra hA
      exact hv (hmu.2 v hA)
    have hchar : _root_.Formalism.EigenvalueLevelCeiling.plc v ∉ S := by
      unfold _root_.Formalism.L2.DIV.GoodPl at hA
      exact hA.2.2
    have hv' : ((Pr.T u : ℕ) : 𝓞 X.F) ∈ v.asIdeal := by
      rw [← hsel v, Ideal.mem_comap]
      simpa using hmem
    have hp := hOk.T_prime u
    have hzero : ((Pr.T u : ℕ) : 𝓞 X.F ⧸ v.asIdeal) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk v.asIdeal)]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hv'
    have : Nontrivial (𝓞 X.F ⧸ v.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr v.isPrime.ne_top
    have hdvd : ringChar (𝓞 X.F ⧸ v.asIdeal) ∣ Pr.T u := (ringChar.spec _ _).mp hzero
    have heq : ringChar (𝓞 X.F ⧸ v.asIdeal) = Pr.T u :=
      ((Nat.dvd_prime hp).mp hdvd).resolve_left CharP.ringChar_ne_one
    apply hchar
    unfold _root_.Formalism.EigenvalueLevelCeiling.plc
    rw [heq]
    exact hT
  · simp at hw

end GlobalTheory.Mem.Col2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayClassFieldFinrankPowPrincipal
section
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.Fld.RayExp

variable {K : Type} (L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem heckeIdeal_pow (χ : (L ≃ₐ[K] L) →* ℂˣ) {I : Ideal (𝓞 K)} (hI : I ≠ 0) (n : ℕ) :
    heckeIdeal L χ (I ^ n) = heckeIdeal L χ I ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, GlobalTheory.NT.Model.heckeIdeal_top]
  | succ n ih => rw [pow_succ, pow_succ, GlobalTheory.NT.Model.heckeIdeal_mul L χ (pow_ne_zero n hI) hI, ih]

theorem heckeIdeal_pow_finrank [IsGalois K L] (χ : (L ≃ₐ[K] L) →* ℂˣ) {𝔮 : Ideal (𝓞 K)}
    (hun : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), ¬ 𝔭.asIdeal ∣ 𝔮 → UnramIn L 𝔭) (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (hc : IsCoprime I 𝔮) : heckeIdeal L χ I ^ Module.finrank K L = 1 := by
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl hI
  | h₂ x hx => rw [isUnit_iff_eq_one.1 hx, GlobalTheory.NT.Model.heckeIdeal_top, one_pow]
  | h₃ a p ha hpp ih =>
    let 𝔭 : HeightOneSpectrum (𝓞 K) := ⟨p, Ideal.isPrime_of_prime hpp, hpp.ne_zero⟩
    have hnd : ¬ 𝔭.asIdeal ∣ 𝔮 := fun hd =>
      hpp.not_unit (hc.of_mul_left_left.isUnit_of_dvd' dvd_rfl hd)
    obtain ⟨σ, hσ⟩ := GlobalTheory.NT.exists_isFrob L 𝔭
    rw [GlobalTheory.NT.Model.heckeIdeal_mul L _ hpp.ne_zero ha, mul_pow, ih ha hc.of_mul_left_right, mul_one,
      show p = 𝔭.asIdeal from rfl, GlobalTheory.NT.Model.heckeIdeal_prime, heckeVal_of_unramIn L χ (hun 𝔭 hnd) hσ,
      ← Units.val_pow_eq_pow_val, ← map_pow, ← IsGalois.card_aut_eq_finrank, pow_card_eq_one', map_one,
      Units.val_one]

theorem pow_finrank_principal : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (𝔮 : Ideal (𝓞 K)), IsRayField K L 𝔮 → ∀ I : Ideal (𝓞 K), I ≠ ⊥ → IsCoprime I 𝔮 →
      ∃ α β : 𝓞 K, RayPair 𝔮 α β ∧ I ^ Module.finrank K L * Ideal.span {β} = Ideal.span {α} := by
  intro K L _ _ _ _ _ 𝔮 ⟨hab, hun, _, hart⟩ I hI hc
  have hI0 : I ≠ 0 := hI
  refine (hart _ (pow_ne_zero _ hI0) hc.pow_left).1 fun χ => ?_
  rw [heckeIdeal_pow L χ hI0, heckeIdeal_pow_finrank L χ hun I hI0 hc]

end GlobalTheory.Mem.Fld.RayExp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SubmodulePatchAtPrimeIsLatticeLocPStatement
section
open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Formalism.L2.Col GlobalTheory.InertExchange
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.submodulePatchAtPrime_isLattice_locP : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (A B : Submodule (𝓞 E) (Sp E n)), Submodule.IsFullLattice E A → Submodule.IsFullLattice E B → Submodule.IsLattice E (patchAt P A B) ∧ ∀ Q : HeightOneSpectrum (𝓞 E), localization₂ Q.asIdeal (patchAt P A B) = localization₂ Q.asIdeal (if Q = P then A else B) := by
  intro E _ _ _ n P A B hA hB
  first
  | exact GlobalTheory.InertExchange.patchAt_isLattice_locP P A B hA hB
  | exact GlobalTheory.InertExchange.patchAt_isLattice_locP P A B hA.toIsLattice hB.toIsLattice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameHeckeCharacterValueViaPowerGenerator
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.ValPow

variable {L : Type} [Field L] [NumberField L]

theorem count_span_int (w : HeightOneSpectrum (𝓞 L)) (a : 𝓞 L) (ha : a ≠ 0) :
    FractionalIdeal.count L w (FractionalIdeal.spanSingleton (𝓞 L)⁰ (algebraMap (𝓞 L) L a)) =
      -WithZero.log (w.valuation L (algebraMap (𝓞 L) L a)) := by
  classical
  rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe L w (by simpa using ha),
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_if_neg _ ha]
  simp

theorem ordF_eq_count (w : HeightOneSpectrum (𝓞 L)) (k : Lˣ) :
    ordF w k = FractionalIdeal.count L w (FractionalIdeal.spanSingleton (𝓞 L)⁰ (k : L)) := by
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 L) (k : L)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact k.ne_zero (by rw [← hab]; simp)
  have ha' : algebraMap (𝓞 L) L a ≠ 0 := by simpa using ha0
  have hb' : algebraMap (𝓞 L) L b ≠ 0 := by simpa using hb0
  unfold ordF
  rw [← hab, div_eq_mul_inv, ← FractionalIdeal.spanSingleton_mul_spanSingleton, ← FractionalIdeal.spanSingleton_inv,
    FractionalIdeal.count_mul L w (FractionalIdeal.spanSingleton_ne_zero_iff.2 ha')
      (inv_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.2 hb')),
    FractionalIdeal.count_inv, count_span_int w a ha0, count_span_int w b hb0, map_mul, map_inv₀,
    WithZero.log_mul ((Valuation.ne_zero_iff _).2 ha') (inv_ne_zero ((Valuation.ne_zero_iff _).2 hb')), WithZero.log_inv]
  ring

theorem locK_eq_one {χ : HChar L} {w : HeightOneSpectrum (𝓞 L)} (h : χ.TameAt w) (k : Lˣ)
    (hk : w.valuation L ((k : L) - 1) < 1) : χ.locK w k = 1 := by
  refine h _ ?_ ?_
  · unfold IsUnitAt
    have h1 : Valued.v ((atFin w k : (w.adicCompletion L)ˣ) : w.adicCompletion L) = w.valuation L (k : L) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w (k : L)
    rw [h1]
    have := (w.valuation L).map_one_add_of_lt hk
    rwa [add_sub_cancel] at this
  · have h1 : ((atFin w k : (w.adicCompletion L)ˣ) : w.adicCompletion L) - 1 =
        algebraMap L (w.adicCompletion L) ((k : L) - 1) := by
      rw [map_sub, map_one]
      rfl
    have h2 : Valued.v (algebraMap L (w.adicCompletion L) ((k : L) - 1)) =
        w.valuation L ((k : L) - 1) := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
    rw [h1, h2]
    rcases eq_or_ne (w.valuation L ((k : L) - 1)) 0 with h0 | h0
    · rw [h0]; exact zero_le
    · rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hk
      rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
      push_cast
      omega

theorem inf_mul_val_pow : ∀ (L : Type) [Field L] [NumberField L] (χ : HChar L) (S : Finset (HeightOneSpectrum (𝓞 L))), (∀ w, w ∉ S → χ.UnrAt w) → (∀ w ∈ S, χ.TameAt w) → ∀ (v : HeightOneSpectrum (𝓞 L)), v ∉ S → ∀ (h : ℕ) (k : Lˣ), FractionalIdeal.spanSingleton (𝓞 L)⁰ (k : L) = (v.asIdeal : FractionalIdeal (𝓞 L)⁰ L) ^ h → (∀ w ∈ S, w.valuation L ((k : L) - 1) < 1) → χ.inf k * χ.val v ^ h = 1 := by
  classical
  intro L _ _ χ S hS hT v hv h k hk h1
  rw [← GlobalTheory.HeckeProduct.hchar_productRule L χ S hS k,
    Finset.prod_eq_one (fun w hw => locK_eq_one (hT w hw) k (h1 w hw)), mul_one]
  congr 1
  rw [finprod_eq_single _ v]
  · rw [finprod_eq_if, if_pos hv, ordF_eq_count, hk, FractionalIdeal.count_pow, FractionalIdeal.count_self, mul_one,
      zpow_natCast]
  · intro w hw
    rw [ordF_eq_count, hk, FractionalIdeal.count_pow, FractionalIdeal.count_maximal_coprime L w (Ne.symm hw), mul_zero,
      zpow_zero, finprod_one]

end GlobalTheory.Mem.ValPow

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryLastRowDivisibleStabilizesLatticesStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.DIV Matrix
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_lastRowDivisible_stabilizes_lattices : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {ST : Finset (Pl E)} {π : 𝓞 E}, BasePi ST π → ∀ (v : HeightOneSpectrum (𝓞 F)) (g : GL (Fin n) (E ⊗[F] v.adicCompletion F)), g ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (v.adicCompletion F) → ((∀ i j, (g : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) i j ∈ intV E v) ∧ ∀ j, j ≠ lastIdx n → ∃ s ∈ intV E v, (g : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) (lastIdx n) j = inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E π) * s) → ((∀ i j, ((g⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) i j ∈ intV E v) ∧ ∀ j, j ≠ lastIdx n → ∃ s ∈ intV E v, ((g⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) (lastIdx n) j = inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E π) * s) → g ∈ stabGL (Formalism.L2.Herm.locL v (baseLb E n ST)) ∧ g ∈ stabGL (baseDualV hc n ST v) ∧ g ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v) (baseKer E n ST)) := by
  first | exact @GlobalTheory.unitary_offRow_stab_three | exact GlobalTheory.unitary_offRow_stab_three | (intros; apply GlobalTheory.unitary_offRow_stab_three <;> assumption)
end

