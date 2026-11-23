module

public import Mathlib
public import Formalism.LocalRingCardinality.HostCls
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle0003
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LocalRingCardinality.DataKerI
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0073
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
public import Formalism.GradedWeylDivisibility.FinalD
public import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelPrimePowSmulMemValueLatticeErase
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TrueWtAddSSNonneg
public import Formalism.LocalToGlobal.Columns.GSetLemmas

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrimeOfLiesOver
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.InertCompare Classical

namespace GlobalTheory.InertCompare

open Formalism.FrobeniusOrbits GlobalTheory.Proof.IdempotentLatticeSequence

theorem ne_of_inert (D : D7) (l : ℕ) (h : IsResidueClassZero D l ∨ IsSg D l) : l ∉ D.host.small ∧ l ≠ D.host.q ∧ l ≠ D.host.d := by
  rcases h with h | h
  · have k := (primeClass_eq_inert_iff D.host.toHostRaw).1 h
    exact ⟨k.1, k.2.1, k.2.2.1⟩
  · have k := (primeClass_eq_signal_iff D.host.toHostRaw).1 h
    exact ⟨k.1, k.2.1, k.2.2.1⟩

theorem primeOf_liesOver {l : ℕ} [Fact l.Prime] {E : Type} [Field E] (ρ : E →+* ℂ_[l]) :
    (primeOf ρ).LiesOver (Ideal.span {(l : ℤ)}) := by
  have := primeOf_isPrime ρ
  refine ⟨(span_prime_isMaximal l Fact.out).eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_⟩
  rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
  exact natCast_mem_primeOf ρ

theorem galE_frob_snd (D : D7) (l : ℕ) [Fact l.Prime] (h2 : l ∉ D.host.small) (hq : l ≠ D.host.q) (hd : l ≠ D.host.d)
    (P : Ideal (𝓞 D.host.E)) [P.IsPrime] [P.LiesOver (Ideal.span {(l : ℤ)})]
    (σ : D.host.E ≃ₐ[ℚ] D.host.E) (hσ : IsArithFrobAt ℤ σ P) :
    (D.host.galE σ).2 = D.R.iota (G.hP D l) := by
  have hc : l.Coprime D.host.condN :=
    (Nat.Prime.coprime_iff_not_dvd Fact.out).2 (UpperTheory.Small.not_dvd_condN D.host Fact.out h2 hq hd)
  have hne : ∃ g, g ∈ Formalism.MainNotions.G.frobSet D l := ⟨_, P, inferInstance, inferInstance, σ, hσ, rfl⟩
  obtain ⟨P₀, hP₀, hL₀, σ₀, hσ₀, hg₀⟩ := Classical.epsilon_spec hne
  have e1 := (D.host.toHostAx.frob_iff l hc P σ).1 hσ
  have e2 := (@Formalism.HC.HostAx.frob_iff _ D.host.toHostAx l _ hc P₀ hP₀ hL₀ σ₀).1 hσ₀
  unfold Formalism.MainNotions.G.hP
  rw [Formalism.HC.Frame.iota_iotaInv, ← hg₀]
  exact congrArg Prod.snd (e1.trans e2.symm)

theorem plGG_posPl_one (D : D7) (l : ℕ) [Fact l.Prime] (h : IsResidueClassZero D l ∨ IsSg D l)
    (P : Ideal (𝓞 D.host.E)) [P.IsPrime] [P.LiesOver (Ideal.span {(l : ℤ)})]
    (σ : D.host.E ≃ₐ[ℚ] D.host.E) (hσ : IsArithFrobAt ℤ σ P) (z : Bool × HH D) :
    plGG D (posPl D l z 1) = plGG D z * D.host.galE σ * D.R.cc := by
  obtain ⟨h2, hq, hd⟩ := ne_of_inert D l h
  have hC := factClassFrob D.R D.host l (UpperTheory.Small.not_dvd_condN D.host Fact.out h2 hq hd) P σ hσ
  have hH := galE_frob_snd D l h2 hq hd P σ hσ
  have hpl : ∀ z : Bool × HH D, plGG D z = ((if z.1 then -1 else 1, 1), D.R.iota z.2) := by
    rintro ⟨b, t⟩
    cases b <;> rfl
  rw [hpl, hpl]
  refine Prod.ext ?_ ?_
  · rcases h with h | h
    · have h1 := hC.2.2.1 h
      have hs : ¬ IsSg D l := fun hs => by
        have := h.symm.trans hs
        cases this
      simp only [Prod.fst_mul, h1, Formalism.HC.Frame.cc, c0, posPl, partner, hs]
      cases z.1 <;> simp
    · have h1 := hC.2.1.1 h
      have hp : (partner D l z.2 1).1 = true := decide_eq_true ⟨h, odd_one⟩
      simp only [Prod.fst_mul, h1, Formalism.HC.Frame.cc, c0, posPl, hp]
      cases z.1 <;> simp
  · simp only [Prod.snd_mul, Formalism.HC.Frame.cc, mul_one, hH, posPl, partner, one_smul]
    rw [Formalism.HC.Frame.iota_add]

theorem exists_frob_step (D : D7) (l : ℕ) [Fact l.Prime] (h : IsResidueClassZero D l ∨ IsSg D l)
    (P : Ideal (𝓞 D.host.E)) [P.IsPrime] [P.LiesOver (Ideal.span {(l : ℤ)})] :
    ∃ φ : D.host.E ≃ₐ[ℚ] D.host.E, IsArithFrobAt ℤ φ P ∧ ∀ z : Bool × HH D,
      plGG D (posPl D l z 1) = plGG D z * D.host.galE φ * D.R.cc := by
  obtain ⟨h2, hq, hd⟩ := ne_of_inert D l h
  obtain ⟨φ, hφ⟩ := (D.host.der.frob l (UpperTheory.Small.not_dvd_condN D.host Fact.out h2 hq hd) P).1
  exact ⟨φ, hφ, plGG_posPl_one D l h P φ hφ⟩

theorem embT_tauPl (D : D7) (z : Bool × HH D) : embT D (tauPl D z) = D.host.emb (plGG D z) := by
  unfold embT tauPl
  rw [Equiv.apply_symm_apply]

theorem emb_mul_galE {R : Ranks} (H : Formalism.BasicNotions.Host R) (g : R.GG) (σ : H.E ≃ₐ[ℚ] H.E) (x : H.E) :
    H.emb (g * H.galE σ) x = H.emb g (σ x) := by
  have he : H.sigmaOf (g * H.galE σ) = H.sigmaOf g * σ := by
    unfold Host.sigmaOf
    rw [map_mul, MulEquiv.symm_apply_apply]
  change H.φ₀ (H.sigmaOf (g * H.galE σ) x) = H.φ₀ ((H.sigmaOf g * σ) x)
  rw [he]

theorem rhoH_posPl_one (D : D7) (l : ℕ) [Fact l.Prime] (lam : Qbar →+* ℂ_[l]) (h : IsResidueClassZero D l ∨ IsSg D l)
    (P : Ideal (𝓞 D.host.E)) [P.IsPrime] [P.LiesOver (Ideal.span {(l : ℤ)})]
    (σ : D.host.E ≃ₐ[ℚ] D.host.E) (hσ : IsArithFrobAt ℤ σ P) (z : Bool × HH D) (x : D.host.E) :
    rhoH D lam (tauPl D (posPl D l z 1)) x = rhoH D lam (tauPl D z) (σ (D.host.conj x)) := by
  rw [rhoH_apply, rhoH_apply, embT_tauPl, embT_tauPl, plGG_posPl_one D l h P σ hσ z,
    ← D.host.galE_conjE, emb_mul_galE, emb_mul_galE]

theorem samePrime_step : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (lam : Qbar →+* ℂ_[l]), (IsResidueClassZero D l ∨ IsSg D l) →
    ∀ z : Bool × HH D, SamePrime (rhoH D lam (tauPl D (posPl D l z 1))) (rhoC D lam (tauPl D z)) := by
  intro D l _ lam h z a
  have := primeOf_isPrime (rhoH D lam (tauPl D z))
  have := primeOf_liesOver (rhoH D lam (tauPl D z))
  obtain ⟨φ, hφ, -⟩ := exists_frob_step D l h (primeOf (rhoH D lam (tauPl D z)))
  rw [rhoH_posPl_one D l lam h _ φ hφ]
  have hc := AlgHom.IsArithFrobAt.comap_eq hφ
  have := Ideal.ext_iff.1 hc (D.host.conj • a)
  exact this

end GlobalTheory.InertCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowDivRowWeight
section
noncomputable section

namespace GlobalTheory.ValCmp

open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.LvT.KerLat

theorem rowGen_diag_monomial_one (R : Type) [CommRing R] {r n : ℕ} (a : Fin r) (d : Fin r × Fin n →₀ ℕ) :
    rowGen R a a (monomial d 1) =
      (1 + Polynomial.X) ^ (Finsupp.weight (rowW r n) d a) * Polynomial.C (monomial d 1) := by
  classical
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    have e : (monomial (f + g) (1 : R) : MvPolynomial (Fin r × Fin n) R) = monomial f 1 * monomial g 1 := by
      rw [monomial_mul, one_mul]
    rw [e, map_mul, hf, hg, map_add (f := _), Pi.add_apply, pow_add, map_mul]
    ring
  | single v c =>
    obtain ⟨b, s⟩ := v
    rw [← X_pow_eq_monomial, map_pow, map_pow]
    unfold rowGen
    rw [aeval_X]
    by_cases h : b = a
    · subst h
      have e : Finsupp.weight (rowW r n) (Finsupp.single (b, s) c) b = c := by
        simp [Finsupp.weight_apply, rowW, Finsupp.sum_single_index]
      rw [e, ← mul_pow]
      simp only [if_true]
      congr 1
      ring
    · have e : Finsupp.weight (rowW r n) (Finsupp.single (b, s) c) a = 0 := by
        simp [Finsupp.weight_apply, rowW, Finsupp.sum_single_index, Ne.symm h]
      rw [e]
      simp [h]

theorem rowGen_diag_homog (R : Type) [CommRing R] {r n : ℕ} (μ : Fin r → ℕ) (a : Fin r)
    (f : MvPolynomial (Fin r × Fin n) R) (hf : IsWeightedHomogeneous (rowW r n) f μ) :
    rowGen R a a f = (1 + Polynomial.X) ^ (μ a) * Polynomial.C f := by
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have e : (monomial d (AddMonoidAlgebra.coeff f d) : MvPolynomial (Fin r × Fin n) R) = AddMonoidAlgebra.coeff f d • monomial d 1 := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [e, map_smul, rowGen_diag_monomial_one, hf (mem_support_iff.mp hd), ← mul_smul_comm,
    Polynomial.smul_C]

theorem rowDiv_rowWeight : ∀ (R : Type) [CommRing R] (r n : ℕ) (μ : Fin r → ℕ)
    (f : MvPolynomial (Fin r × Fin n) R), IsWeightedHomogeneous (rowW r n) f μ →
    (∀ (a b : Fin r) (k : ℕ), ∃ μ' : Fin r → ℕ, IsWeightedHomogeneous (rowW r n) (rowDiv R a b k f) μ') ∧
      ∀ (a : Fin r) (k : ℕ), rowDiv R a a k f = ((μ a).choose k) • f := by
  intro R _ r n μ f hf
  refine ⟨fun a b k => ?_, fun a k => ?_⟩
  · have hZ : IsWeightedHomogeneous (rowZ r n) f (fun i => (μ i : ℤ)) := by
      intro d hd
      funext i
      rw [weight_rowZ, hf hd]
    have h := rowDiv_shift R _ a b k f hZ
    refine ⟨fun i => ((((fun i => (μ i : ℤ)) + k • (Pi.single a 1 - Pi.single b 1) : Fin r → ℤ)) i).toNat,
      fun d hd => ?_⟩
    funext i
    rw [← h hd, weight_rowZ, Int.toNat_natCast]
  · unfold rowDiv
    rw [rowGen_diag_homog R μ a f hf, Polynomial.coeff_mul_C, Polynomial.coeff_one_add_X_pow, nsmul_eq_mul]

end GlobalTheory.ValCmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SumFibreEqSumOrbits
section
noncomputable section

namespace GlobalTheory.GO

open NumberField _root_.Formalism.L2.Col Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Forms

theorem sum_inv_eq_sum_orbits {K M H X : Type} [Field K] [CharZero K] [AddCommGroup M] [Module K M] [Group H] [Finite H]
    [MulAction H X] [Fintype X] [Fintype (MulAction.orbitRel.Quotient H X)] (F : X → M)
    (hF : ∀ (g : H) (x : X), F (g • x) = F x) :
    ((Nat.card H : K))⁻¹ • ∑ x, F x =
      ∑ q : MulAction.orbitRel.Quotient H X, ((Nat.card (MulAction.stabilizer H q.out) : K))⁻¹ • F q.out := by
  classical
  rw [← Finset.sum_fiberwise (s := Finset.univ) (g := fun x : X => (Quotient.mk'' x : MulAction.orbitRel.Quotient H X)),
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  have hmem : ∀ x : X, (Quotient.mk'' x : MulAction.orbitRel.Quotient H X) = q ↔ x ∈ MulAction.orbit H q.out := by
    intro x
    conv_lhs => rw [← Quotient.out_eq' q]
    rw [Quotient.eq'']
    exact MulAction.orbitRel_apply
  rw [Finset.sum_congr rfl (g := fun _ => F q.out) (by
    intro x hx
    obtain ⟨g, rfl⟩ := (hmem x).1 (Finset.mem_filter.1 hx).2
    exact hF g _), Finset.sum_const]
  have hc : (Finset.univ.filter fun x : X => (Quotient.mk'' x : MulAction.orbitRel.Quotient H X) = q).card
      = Nat.card (MulAction.orbit H q.out) := by
    symm
    refine Nat.subtype_card _ fun x => ?_
    rw [Finset.mem_filter, ← hmem]
    simp
  have hm : Nat.card (MulAction.orbit H q.out) * Nat.card (MulAction.stabilizer H q.out) = Nat.card H := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup H q.out)
  have h1 : (Nat.card (MulAction.stabilizer H q.out) : K) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have h2 : (Nat.card H : K) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  rw [hc, ← Nat.cast_smul_eq_nsmul K, smul_smul]
  congr 1
  have : (Nat.card (MulAction.orbit H q.out) : K) * Nat.card (MulAction.stabilizer H q.out) = Nat.card H := by
    exact_mod_cast congrArg (Nat.cast : ℕ → K) hm
  field_simp
  rw [← this]

theorem card_stabilizer_smul {G D : Type} [Group G] [MulAction G D] (g : G) (d : D) :
    Nat.card (MulAction.stabilizer G (g • d)) = Nat.card (MulAction.stabilizer G d) :=
  (Nat.card_congr (MulAction.stabilizerEquivStabilizer (g := g) (a := d) (b := g • d) rfl).toEquiv).symm

theorem sum_fibre_eq_sum_orbits {K M G D D₀ : Type} [Field K] [CharZero K] [AddCommGroup M] [Module K M] [Group G]
    [MulAction G D] [MulAction G D₀] (pr : D → D₀) (hpr : ∀ (g : G) (d : D), pr (g • d) = g • pr d)
    [Fintype (MulAction.orbitRel.Quotient G D₀)] [Fintype (MulAction.orbitRel.Quotient G D)]
    (hs : ∀ x : D₀, Finite (MulAction.stabilizer G x)) [∀ x : D₀, Fintype (fibre pr hpr x)] (F : D → M)
    (hF : ∀ (g : G) (x : D), F (g • x) = F x) :
    ∑ c : MulAction.orbitRel.Quotient G D₀, ((Nat.card (MulAction.stabilizer G c.out) : K))⁻¹ •
        ∑ y : fibre pr hpr c.out, F y =
      ∑ q : MulAction.orbitRel.Quotient G D, ((Nat.card (MulAction.stabilizer G q.out) : K))⁻¹ • F q.out := by
  classical
  let _ : ∀ x : D₀, Fintype (MulAction.orbitRel.Quotient (MulAction.stabilizer G x) (fibre pr hpr x)) :=
    fun x => Fintype.ofFinite _
  rw [← (orbitsFib pr hpr Quotient.out (fun c => Quotient.out_eq' c)).sum_comp, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun c _ => ?_
  have := hs c.out
  rw [sum_inv_eq_sum_orbits (H := MulAction.stabilizer G c.out) (fun y : fibre pr hpr c.out => F y)
    (fun g y => hF (g : G) (y : D))]
  refine Finset.sum_congr rfl fun q _ => ?_
  have h1 : (orbitsFib pr hpr Quotient.out (fun c => Quotient.out_eq' c)) ⟨c, q⟩
      = (Quotient.mk'' ((q.out : fibre pr hpr c.out) : D) : MulAction.orbitRel.Quotient G D) := by
    conv_lhs => rw [← Quotient.out_eq' q]
    rfl
  obtain ⟨g, hg⟩ : ∃ g : G, g • ((q.out : fibre pr hpr c.out) : D) =
      ((orbitsFib pr hpr Quotient.out (fun c => Quotient.out_eq' c)) ⟨c, q⟩).out := by
    rw [h1]
    exact Quotient.exact' (Quotient.out_eq' (Quotient.mk'' ((q.out : fibre pr hpr c.out) : D) :
      MulAction.orbitRel.Quotient G D))
  rw [← hg, hF, card_stabilizer_smul, fibre_card_stab]

section Pairs

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S₀ S S₁ : GSD K} {Y : Cpl S}

def cplFibreEquiv (Y : Cpl S) (x : S.D) :
    fibre (G := S.G) (fun p : Y.Pts => p.1.1) (fun _ _ => rfl) x ≃ Y.ys x where
  toFun p := ⟨p.1.1.2, by
    have h1 : p.1.1.1 = x := p.2
    exact (congrArg (fun z => p.1.1.2 ∈ Y.ys z) h1).mp p.1.2⟩
  invFun y := ⟨⟨(x, y.1), y.2⟩, rfl⟩
  left_inv p := Subtype.ext (Subtype.ext (Prod.ext (show p.1.1.1 = x from p.2).symm rfl))
  right_inv _ := rfl

theorem cplGSD_ok (Y : Cpl S) (h : S.Ok) : (cplGSD S Y).Ok := by
  refine {
    fin_orb := ?_
    fin_stab := ?_
    nab_smul := fun g d => h.nab_smul g d.1.1
    del_smul := fun g d => h.del_smul g d.1.1
    inv := h.inv }
  · have := h.fin_orb
    have : ∀ x : S.D, Finite (fibre (G := S.G) (fun p : Y.Pts => p.1.1) (fun _ _ => rfl) x) := fun x =>
      have := (Y.fin x).to_subtype
      Finite.of_equiv _ (cplFibreEquiv Y x).symm
    exact Finite.of_equiv _ (orbitsFib (G := S.G) (fun p : Y.Pts => p.1.1) (fun _ _ => rfl) Quotient.out
      (fun c => Quotient.out_eq' c))
  · intro d
    have := h.fin_stab d.1.1
    have hle : MulAction.stabilizer S.G d ≤ MulAction.stabilizer S.G d.1.1 := fun g hg =>
      congrArg (fun p : Y.Pts => p.1.1) hg
    exact Finite.of_injective _ (Subgroup.inclusion_injective hle)

def cplKer1 (A : CplKer S₀ S S₁ Y) : ClsKer S₀ (cplGSD S Y) where
  k d₀ d := A.k1 d₀ d.1.1 d.1.2
  equiv g₀ g d₀ d := A.equiv1 g₀ g d₀ d.1.1 d.1.2

def cplKer2 (A : CplKer S₀ S S₁ Y) : ClsKer (cplGSD S Y) S₁ where
  k d d₁ := A.k2 d.1.1 d.1.2 d₁
  equiv g g₁ d d₁ := A.equiv2 g g₁ d.1.1 d.1.2 d₁

theorem cpl_comp_k (A : CplKer S₀ S S₁ Y) (h : S.Ok) (d₀ : S₀.D) (d₁ : S₁.D) :
    (A.comp h S.outSec).k d₀ d₁ =
      letI := (cplGSD_ok Y h).fintypeCl
      ∑ q : (cplGSD S Y).Cl, ((((cplGSD S Y).toCSDOf (cplGSD_ok Y h) (cplGSD S Y).outSec).wt q : K))⁻¹ •
        ((cplKer2 A).k ((cplGSD S Y).outSec.rep q) d₁) ∘ₗ ((cplKer1 A).k d₀ ((cplGSD S Y).outSec.rep q)) := by
  let i1 : Fintype (MulAction.orbitRel.Quotient S.G S.D) := h.fintypeCl
  let i2 : Fintype (MulAction.orbitRel.Quotient S.G Y.Pts) := (cplGSD_ok Y h).fintypeCl
  let i3 : ∀ x : S.D, Fintype (fibre (G := S.G) (fun p : Y.Pts => p.1.1) (fun _ _ => rfl) x) := fun x =>
    have := (Y.fin x).to_subtype
    have := Finite.of_equiv _ (cplFibreEquiv Y x).symm
    Fintype.ofFinite _
  have key := sum_fibre_eq_sum_orbits (K := K) (G := S.G) (fun p : Y.Pts => p.1.1) (fun _ _ => rfl) h.fin_stab
    (fun p : Y.Pts => (A.k2 p.1.1 p.1.2 d₁) ∘ₗ (A.k1 d₀ p.1.1 p.1.2)) (by
      intro g p
      have e1 := A.equiv1 1 g d₀ p.1.1 p.1.2
      have e2 := A.equiv2 g 1 p.1.1 p.1.2 d₁
      rw [one_smul, inv_one, map_one] at e1
      rw [one_smul, map_one] at e2
      show (A.k2 (g • p.1.1) (g • p.1.2) d₁) ∘ₗ (A.k1 d₀ (g • p.1.1) (g • p.1.2)) = _
      rw [e1, e2]
      ext x
      simp only [LinearMap.comp_apply, one_apply_eq_self]
      rw [← mul_apply_eq_comp (S.ρ g⁻¹), ← map_mul, inv_mul_cancel, map_one, one_apply_eq_self])
  simp only [CSD.wt, ← Nat.card_eq_fintype_card]
  refine Eq.trans ?_ key
  show ∑ c : S.Cl, _ = _
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [CSD.wt, ← Nat.card_eq_fintype_card]
  congr 1
  let _ : Fintype (Y.ys c.out) := (Y.fin c.out).fintype
  refine (Finset.sum_subtype (p := fun y => y ∈ Y.ys c.out) (F := inferInstance) _
    (fun y => (Y.fin _).mem_toFinset) _).trans ?_
  exact ((cplFibreEquiv Y c.out).symm.sum_comp
    (fun y => (A.k2 y.1.1.1 y.1.1.2 d₁) ∘ₗ (A.k1 d₀ y.1.1.1 y.1.1.2)))

end Pairs

end GlobalTheory.GO
end
end

