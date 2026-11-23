module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.EtaleComparisonMapOfFacts
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0168
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CechDifferentialPullback.Bridge
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0007
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.IsEpCont
public import GroundTheory.GlobalFields.TateThesis.TateMain
public import GroundTheory.AutomorphicForms.GL2.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBruhatUniformSummableMajorant
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0169

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AcrisZeroImageDividedPower
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.LogEpsP

variable {l : ℕ} [Fact l.Prime]

theorem cris_eq_zero (A : PAlg l) (n : ℕ) {y : Acris l}
    (hy : y ∈ Ideal.span {(l : Acris l)} ^ n) : A.cris n y = 0 := by
  rw [Ideal.span_singleton_pow] at hy
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  rw [map_mul, map_pow, map_natCast, PAlg.pow_l_acr, mul_zero]

theorem cris_log (A : PAlg l) (n : ℕ) {x : Ainf l} (hx : x ∈ RingHom.ker (theta0 l)) :
    A.cris n (ACris.log hx) = ∑ k ∈ Finset.range (l * n), A.cris n (ACris.logTerm hx k) := by
  obtain ⟨N, hN⟩ := ACris.isAdicSum_log hx n
  have h2 := cris_eq_zero A n (hN (max N (l * n)) (le_max_left _ _))
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sub, sub_eq_zero, map_sum,
    ← Finset.sum_range_add_sum_Ico _ (le_max_right N (l * n)),
    Finset.sum_eq_zero (s := Finset.Ico (l * n) (max N (l * n))) (fun k hk =>
      cris_eq_zero A n (ACris.logTerm_mem hx (Finset.mem_Ico.1 hk).1)), add_zero] at h2
  exact h2

theorem cris_logTerm (A : PAlg l) (n k : ℕ) {x : Ainf l} (hx : x ∈ RingHom.ker (theta0 l)) :
    A.cris n (ACris.logTerm hx k) =
      (-1) ^ k * (k.factorial : A.Acr n) * A.mkAcr n (A.cris0 (ACris.dpowZero hx (k + 1))) := by
  rw [ACris.logTerm, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    PAlg.cris_of, ACris.logTermZero]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_mul, map_pow, map_neg, map_one, map_natCast]

theorem acrisZero_image_divided_power (A : PAlg l) (k : ℕ) {x : Ainf l} (hx : x ∈ RingHom.ker (theta0 l)) :
    (A.cris0 (ACris.dpowZero hx k)).1 = dpw k (WittVector.map A.s x) :=
  awayW_dpw A.s k (ACris.isUnit_natCast (K := ℂ_[l]) (p := l) k.factorial_ne_zero) x

theorem map_mu (A : PAlg l) (e : Ob l) :
    WittVector.map A.s (AInf.mu (K := ℂ_[l]) (p := l) e) = WittVector.teichmuller l (A.s e) - 1 := by
  rw [AInf.mu, map_sub, map_one, WittVector.map_teichmuller]

end GlobalTheory.CompanionTheory.LogEpsP

theorem GlobalTheory.CompanionTheory.LogEpsP.logEps : CrystallineSemistableComparison.E.LogEps := by
  intro l _ A n
  refine ⟨fun k => A.cris0 (ACris.dpowZero (ACris.mu_mem_ker (untilt_epsilon (p := l))) k), fun k => ?_, ?_⟩
  · rw [GlobalTheory.CompanionTheory.LogEpsP.acrisZero_image_divided_power, GlobalTheory.CompanionTheory.LogEpsP.map_mu]
  · rw [ACris.periodT, GlobalTheory.CompanionTheory.LogEpsP.cris_log]
    exact Finset.sum_congr rfl fun k _ => GlobalTheory.CompanionTheory.LogEpsP.cris_logTerm A n k _
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechShortExactPullCompatStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_short_exact_pull_compat : ∀ {X Y : TopCat.{0}} (f : X ⟶ Y) {κ ι : Type} (V : κ → Opens Y) (U : ι → Opens X) (τ : ι → κ)
    (hτ : ∀ i, U i ≤ (Opens.map f).obj (V (τ i))) {F I Q : (Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{0}}
    {F' I' Q' : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{0}} {g₁ : F ⟶ I} {g₂ : I ⟶ Q} {g₁' : F' ⟶ I'} {g₂' : I' ⟶ Q'}
    (hC : IsCechShortExact V g₁ g₂) (hC' : IsCechShortExact U g₁' g₂') (φ₁ : F ⟶ (Opens.map f).op ⋙ F')
    (φ₂ : I ⟶ (Opens.map f).op ⋙ I') (φ₃ : Q ⟶ (Opens.map f).op ⋙ Q')
    (h₁₂ : ∀ W x, φ₂.app W (g₁.app W x) = g₁'.app _ (φ₁.app W x))
    (h₂₃ : ∀ W x, φ₃.app W (g₂.app W x) = g₂'.app _ (φ₂.app W x)) (n : ℕ) (σ : cocycles Q V n),
    cechPullH f φ₁ V U τ hτ (n + 1) (hC.delta n σ) =
      hC'.delta n ⟨pullCoch f φ₃ V U τ hτ n σ.1, pullCoch_mem_cocycles f φ₃ V U τ hτ σ.2⟩ := by
  intro X Y f κ ι V U τ hτ F I Q F' I' Q' g₁ g₂ g₁' g₂' hC hC' φ₁ φ₂ φ₃ h₁₂ h₂₃ n σ
  obtain ⟨t, ρ, hρ, ht, hρt, hc⟩ := hC.delta_spec n σ
  have ht' : push U g₂' n (pullCoch f φ₂ V U τ hτ n t) = pullCoch f φ₃ V U τ hτ n σ.1 := by
    rw [GlobalTheory.CompanionTheory.OmCechDelta.push_pullCoch f V U τ hτ g₂ g₂' φ₂ φ₃ h₂₃ n t, ht]
  have hρt' : push U g₁' (n + 1) (pullCoch f φ₁ V U τ hτ (n + 1) ρ) =
      d I' U n (pullCoch f φ₂ V U τ hτ n t) := by
    rw [GlobalTheory.CompanionTheory.OmCechDelta.push_pullCoch f V U τ hτ g₁ g₁' φ₁ φ₂ h₁₂ (n + 1) ρ,
      hρt, pullCoch_d]
  have hρ' : d F' U (n + 1) (pullCoch f φ₁ V U τ hτ (n + 1) ρ) = 0 := by
    rw [← pullCoch_d, hρ, map_zero]
  rw [hc, cechPullH_cls]
  exact hC'.deltaRel_unique
    ⟨pullCoch f φ₂ V U τ hτ n t, pullCoch f φ₁ V U τ hτ (n + 1) ρ, hρ', ht', hρt', rfl⟩
    (hC'.delta_spec n ⟨pullCoch f φ₃ V U τ hτ n σ.1, pullCoch_mem_cocycles f φ₃ V U τ hτ σ.2⟩)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartUnionLeSite
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeSite

theorem wU_le_KS : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (D : E.LineData X) {N m : ℕ}
    (i : X ⟶ PSpace K N) (y : Fin m → MvPolynomial (Fin (N + 1)) K) (s : ℕ), IsTautologicalLineAt D N i → wU q i y s ≤ KS q s (𝒱D D) := by
  intro K _ X q D N m i y s hO T hT
  obtain ⟨k, hQ, V, ⟨j, rfl⟩, hV⟩ := hT
  exact ⟨hQ, wch i j, _root_.GlobalTheory.CompanionTheory.ConeWchMem.main D N i hO j, fun x hx => (hV hx).2⟩

end GlobalTheory.CompanionTheory.ConeSite
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChernClassUniqueOfLiftAndLog
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EtChern

theorem restrict_id_pull {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R) (x : H (𝟭 C ⋙ F) 2) (x' : H F 2)
    (h : x = (Mor.restrict F (𝟭 C)).pull 2 x') : x = x' := by
  subst h
  obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x'
  rfl

theorem chern_class_unique_of_lift_and_log : CrystallineSemistableComparison.E.LiftEx → CrystallineSemistableComparison.E.LogEx → CrystallineSemistableComparison.E.FirstChernUniqueEtale := by
  intro hL hG l _ H O _ X q κ D hE y y' hy hy'
  obtain ⟨Λ⟩ := (hL l H O X q κ (El (PX q κ)) (𝟭 _) D).2 hE
  funext n
  obtain ⟨z, hz, hc, e⟩ := hy (El (PX q κ)) (𝟭 _) Λ n
  obtain ⟨z', hz', hc', e'⟩ := hy' (El (PX q κ)) (𝟭 _) Λ n
  have hzz : z = z' := by
    funext s
    exact (hG l _ n).2.1 _ _ _ (hc s) (hc' s)
  subst hzz
  have e1 := restrict_id_pull _ _ _ e
  have e2 := restrict_id_pull _ _ _ e'
  exact e1.symm.trans e2

end GlobalTheory.CompanionTheory.EtChern
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoeffIterateVerschiebung
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.LcSp

section Witt

variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] [CharP R p]

theorem coeff_iterate_verschiebung (m : ℕ) (y : WittVector p R) (i : ℕ) (h : i < m) :
    (WittVector.verschiebung^[m] y).coeff i = 0 := by
  induction m generalizing i with
  | zero => omega
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    cases i with
    | zero => exact WittVector.verschiebung_coeff_zero _
    | succ i =>
      rw [WittVector.verschiebung_coeff_succ]
      exact ih i (by omega)

theorem idem_eq_zero (u : WittVector p R) (hu : u * u = u) (h0 : u.coeff 0 = 0) : u = 0 := by
  have key : ∀ n, ∀ i < n + 1, u.coeff i = 0 := by
    intro n
    induction n with
    | zero =>
      intro i hi
      obtain rfl : i = 0 := by omega
      exact h0
    | succ n ih =>
      intro i hi
      by_cases h : i < n + 1
      · exact ih i h
      obtain rfl : i = n + 1 := by omega
      obtain ⟨y, e⟩ : ∃ y, u = WittVector.verschiebung^[n + 1] y := ⟨_, WittVector.eq_iterate_verschiebung ih⟩
      have e2 : u = WittVector.verschiebung^[(n + 1) + (n + 1)]
          (WittVector.frobenius^[n + 1] y * WittVector.frobenius^[n + 1] y) := by
        rw [← WittVector.iterate_verschiebung_mul, ← e, hu]
      rw [e2]
      exact coeff_iterate_verschiebung _ _ _ (by omega)
  ext i
  rw [key i i (by omega)]
  simp

theorem sum_teichmuller {ι : Type} [Fintype ι] (e : ι → R) (he : CompleteOrthogonalIdempotents e) :
    ∑ i, WittVector.teichmuller p (e i) = (1 : WittVector p R) := by
  have ho : OrthogonalIdempotents fun i => WittVector.teichmuller p (e i) :=
    { idem := fun i => by
        change _ * _ = _
        rw [← map_mul, (he.idem i).eq]
      ortho := fun i j hij => by
        change _ * _ = _
        rw [← map_mul, he.ortho hij, WittVector.teichmuller_zero] }
  have hs : IsIdempotentElem (∑ i, WittVector.teichmuller p (e i)) := ho.isIdempotentElem_sum
  have h1 : (1 : WittVector p R) - ∑ i, WittVector.teichmuller p (e i) = 0 := by
    refine idem_eq_zero _ hs.one_sub.eq ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← WittVector.constantCoeff_apply, map_sub, map_one, map_sum]
    simp only [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]
    rw [he.complete, sub_self]
  exact (sub_eq_zero.1 h1).symm

end Witt

variable {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ)

theorem sum_teich {ι : Type} [Fintype ι] (e : ι → A.A) (he : CompleteOrthogonalIdempotents e) :
    ∑ i, WittVector.teichmuller l (e i) = (1 : A.W) := by
  rcases subsingleton_or_nontrivial A.A with h | h
  · exact WittVector.ext fun _ => Subsingleton.elim _ _
  · haveI : CharP A.A l := (CharP.charP_iff_prime_eq_zero Fact.out).2 A.natCast_l
    exact sum_teichmuller e he

theorem acr_ext {ι : Type} [Fintype ι] (e : ι → A.A) (he : CompleteOrthogonalIdempotents e) {x y : A.Acr n}
    (h : ∀ i, A.toAcr n (WittVector.teichmuller l (e i)) * x = A.toAcr n (WittVector.teichmuller l (e i)) * y) :
    x = y := by
  have hs : ∑ i, A.toAcr n (WittVector.teichmuller l (e i)) = 1 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, sum_teich A e he, map_one]
  calc x = (∑ i, A.toAcr n (WittVector.teichmuller l (e i))) * x := by rw [hs, one_mul]
    _ = (∑ i, A.toAcr n (WittVector.teichmuller l (e i))) * y := by
      simp only [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => h i
    _ = y := by rw [hs, one_mul]

theorem exists_cast : ∃ c : ZMod (l ^ n) →+* A.Acr n, ∀ a, c a = (a.val : A.Acr n) := by
  haveI : CharP (A.Acr n) (ringChar (A.Acr n)) := ringChar.charP _
  have hd : ringChar (A.Acr n) ∣ l ^ n :=
    (CharP.cast_eq_zero_iff (A.Acr n) (ringChar (A.Acr n)) (l ^ n)).1 (by
      rw [Nat.cast_pow]
      exact A.pow_l_acr n)
  refine ⟨ZMod.castHom hd _, fun a => ?_⟩
  rw [ZMod.castHom_apply, ZMod.natCast_val]

variable {A n}

section Main

variable (hI : LcIdem) (H : RIn l) (hA : A.IsTest)
include hI H hA

theorem exists_isLcA (f : LocallyConstant (SU A) (ZMod (l ^ n))) : ∃ x, IsLcA A n f x := by
  obtain ⟨e, he, -, h2⟩ := hI l H A hA (ZMod (l ^ n)) f
  refine ⟨∑ a, A.toAcr n (WittVector.teichmuller l (e a)) * (a.val : A.Acr n), fun e' a he' hf => ?_⟩
  have h3 : e' * e a = e' := h2 e' a he' hf
  rw [Finset.mul_sum, Finset.sum_eq_single a]
  · rw [← mul_assoc, ← map_mul, ← map_mul, h3]
  · intro b _ hb
    have h4 : e' * e b = 0 := by
      calc e' * e b = e' * e a * e b := by rw [h3]
        _ = 0 := by rw [mul_assoc, he.ortho hb.symm, mul_zero]
    rw [← mul_assoc, ← map_mul, ← map_mul, h4, WittVector.teichmuller_zero, map_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ a) h

theorem isLcA_unique {f : LocallyConstant (SU A) (ZMod (l ^ n))} {x y : A.Acr n}
    (hx : IsLcA A n f x) (hy : IsLcA A n f y) : x = y := by
  obtain ⟨e, he, h1, -⟩ := hI l H A hA (ZMod (l ^ n)) f
  refine acr_ext A n e he fun a => ?_
  have hf : ∀ p : PrimeSpectrum A.Ug, algebraMap A.U A.Ug (A.sharp (e a)) ∉ p.asIdeal → f p = a :=
    fun p hp => (h1 a p).1 hp
  rw [hx (e a) a (he.idem a) hf, hy (e a) a (he.idem a) hf]

theorem isLcA_one : IsLcA A n 1 1 := by
  obtain ⟨c, hc⟩ := exists_cast A n
  obtain ⟨e, he, -, h2⟩ := hI l H A hA (ZMod (l ^ n)) 1
  intro e' a he' hf
  by_cases ha : a = 1
  · subst ha
    rw [← hc, map_one]
  · have h3 : e' * e a = e' := h2 e' a he' hf
    have h4 : e' * e 1 = e' := h2 e' 1 he' fun _ _ => rfl
    have h5 : e' = 0 := by
      calc e' = e' * e 1 * e a := by rw [h4, h3]
        _ = 0 := by rw [mul_assoc, he.ortho (Ne.symm ha), mul_zero]
    rw [h5, WittVector.teichmuller_zero, map_zero, zero_mul, zero_mul]

theorem exists_pair (f g : LocallyConstant (SU A) (ZMod (l ^ n))) :
    ∃ e : ZMod (l ^ n) × ZMod (l ^ n) → A.A, CompleteOrthogonalIdempotents e ∧
      ∀ (ab : ZMod (l ^ n) × ZMod (l ^ n)) (p : PrimeSpectrum A.Ug),
        algebraMap A.U A.Ug (A.sharp (e ab)) ∉ p.asIdeal → f p = ab.1 ∧ g p = ab.2 := by
  let h : LocallyConstant (SU A) (ZMod (l ^ n) × ZMod (l ^ n)) :=
    ⟨fun p => (f p, g p), f.isLocallyConstant.prodMk g.isLocallyConstant⟩
  obtain ⟨e, he, h1, -⟩ := hI l H A hA _ h
  refine ⟨e, he, fun ab p hp => ?_⟩
  have h2 : (f p, g p) = ab := (h1 ab p).1 hp
  exact ⟨congrArg Prod.fst h2, congrArg Prod.snd h2⟩

theorem isLcA_add {f g : LocallyConstant (SU A) (ZMod (l ^ n))} {x y z : A.Acr n}
    (hx : IsLcA A n f x) (hy : IsLcA A n g y) (hz : IsLcA A n (f + g) z) : z = x + y := by
  obtain ⟨e, he, h⟩ := exists_pair hI H hA f g
  obtain ⟨c, hc⟩ := exists_cast A n
  refine acr_ext A n e he fun ab => ?_
  have h1 := hx (e ab) ab.1 (he.idem ab) fun p hp => (h ab p hp).1
  have h2 := hy (e ab) ab.2 (he.idem ab) fun p hp => (h ab p hp).2
  have h3 := hz (e ab) (ab.1 + ab.2) (he.idem ab) fun p hp => by
    change f p + g p = _
    rw [(h ab p hp).1, (h ab p hp).2]
  rw [h3, mul_add, h1, h2, ← hc, ← hc, ← hc, map_add (f := _), mul_add]

theorem isLcA_mul {f g : LocallyConstant (SU A) (ZMod (l ^ n))} {x y z : A.Acr n}
    (hx : IsLcA A n f x) (hy : IsLcA A n g y) (hz : IsLcA A n (f * g) z) : z = x * y := by
  obtain ⟨e, he, h⟩ := exists_pair hI H hA f g
  obtain ⟨c, hc⟩ := exists_cast A n
  refine acr_ext A n e he fun ab => ?_
  have h1 := hx (e ab) ab.1 (he.idem ab) fun p hp => (h ab p hp).1
  have h2 := hy (e ab) ab.2 (he.idem ab) fun p hp => (h ab p hp).2
  have h3 := hz (e ab) (ab.1 * ab.2) (he.idem ab) fun p hp => by
    change f p * g p = _
    rw [(h ab p hp).1, (h ab p hp).2]
  have ht : A.toAcr n (WittVector.teichmuller l (e ab)) * A.toAcr n (WittVector.teichmuller l (e ab)) =
      A.toAcr n (WittVector.teichmuller l (e ab)) := by
    rw [← map_mul, ← map_mul, (he.idem ab).eq]
  rw [← hc] at h1 h2 h3
  calc _ = A.toAcr n (WittVector.teichmuller l (e ab)) * (c ab.1 * c ab.2) := by rw [h3, map_mul]
    _ = (A.toAcr n (WittVector.teichmuller l (e ab)) * c ab.1) * (A.toAcr n (WittVector.teichmuller l (e ab)) * c ab.2) := by
      rw [mul_mul_mul_comm, ht]
    _ = (A.toAcr n (WittVector.teichmuller l (e ab)) * x) * (A.toAcr n (WittVector.teichmuller l (e ab)) * y) := by
      rw [h1, h2]
    _ = _ := by rw [mul_mul_mul_comm, ht]

end Main

theorem lcSpec_of_lcIdem : CrystallineSemistableComparison.E.LcIdem → CrystallineSemistableComparison.E.LcSpec := by
  intro hI l _ H A hA n
  have P : ∃ κ : LocallyConstant (SU A) (ZMod (l ^ n)) →+ A.Acr n, ∀ f, IsLcA A n f (κ f) := by
    choose k hk using exists_isLcA (n := n) hI H hA
    exact ⟨AddMonoidHom.mk' k fun f g => isLcA_add hI H hA (hk f) (hk g) (hk (f + g)), hk⟩
  have S : ∀ f, IsLcA A n f (lcA A n f) := pick_spec P
  refine ⟨S, isLcA_unique hI H hA (S 1) (isLcA_one hI H hA),
    fun f g => isLcA_mul hI H hA (S f) (S g) (S (f * g)), fun f e he h => ?_⟩
  refine acr_ext A n e he fun a => ?_
  rw [S f (e a) a (he.idem a) (h a), Finset.mul_sum, Finset.sum_eq_single a]
  · rw [← mul_assoc, ← map_mul, ← map_mul, (he.idem a).eq]
  · intro b _ hb
    rw [← mul_assoc, ← map_mul, ← map_mul, he.ortho hb.symm, WittVector.teichmuller_zero, map_zero, zero_mul]
  · intro h'
    exact absurd (Finset.mem_univ a) h'

end GlobalTheory.CompanionTheory.LcSp
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousAdeleWeight
section
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.EpConvB

open NumberField NumberField.mixedEmbedding IsDedekindDomain Matrix MeasureTheory Filter _root_.Topology
open scoped NumberField.AdeleRing SchwartzMap Classical nonZeroDivisors
open GroundTheory.Global GroundTheory.Automorphic

set_option synthInstance.maxSize 1000

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

def adeleWeight (L : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (A : ℕ) (y : 𝔸[K]) : ℝ :=
  if y.2 ∈ idealFiniteAdeles L then ((1 + ‖homeomorphMixedSpace K y.1‖) ^ A)⁻¹ else 0

theorem adeleWeight_nonneg (L : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (A : ℕ) (y : 𝔸[K]) :
    0 ≤ adeleWeight L A y := by
  unfold adeleWeight
  split_ifs <;> positivity

theorem adeleWeight_le_one (L : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (A : ℕ) (y : 𝔸[K]) :
    adeleWeight L A y ≤ 1 := by
  unfold adeleWeight
  split_ifs
  · exact inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [norm_nonneg (homeomorphMixedSpace K y.1)]))
  · exact zero_le_one

theorem adeleWeight_mono {L L' : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (h : (L : FractionalIdeal (𝓞 K)⁰ K) ≤ L') (A : ℕ) (y : 𝔸[K]) :
    adeleWeight L A y ≤ adeleWeight L' A y := by
  unfold adeleWeight
  by_cases h1 : y.2 ∈ idealFiniteAdeles L
  · have h2 : y.2 ∈ idealFiniteAdeles L' := idealFiniteAdeles_subset h h1
    simp only [if_pos h1, if_pos h2, le_refl]
  · rw [if_neg h1]
    split_ifs
    · positivity
    · exact le_rfl

@[simp] theorem adeleWeight_zero (L : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (A : ℕ) :
    adeleWeight L A (0 : 𝔸[K]) = 1 := by
  have h0 : (0 : 𝔸[K]).2 ∈ idealFiniteAdeles L := zero_mem _
  have h1 : homeomorphMixedSpace K (0 : 𝔸[K]).1 = 0 := map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace K)
  unfold adeleWeight
  rw [if_pos h0, h1]
  simp

theorem continuous_adeleWeight (L : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (A : ℕ) :
    Continuous (adeleWeight (K := K) L A) := by
  have hc : IsClopen ((idealFiniteAdeles L : AddSubgroup 𝔸ᶠ[K]) : Set 𝔸ᶠ[K]) :=
    ⟨AddSubgroup.isClosed_of_isOpen _ (isOpen_idealFiniteAdeles L), isOpen_idealFiniteAdeles L⟩
  have hc' : IsClopen {y : 𝔸[K] | y.2 ∈ idealFiniteAdeles L} := hc.preimage continuous_snd
  have hf : Continuous fun y : 𝔸[K] ↦ ((1 + ‖homeomorphMixedSpace K y.1‖) ^ A)⁻¹ := by
    refine Continuous.inv₀ (by fun_prop) fun y ↦ ?_
    have := norm_nonneg (homeomorphMixedSpace K y.1)
    positivity
  have : adeleWeight (K := K) L A = Set.indicator {y : 𝔸[K] | y.2 ∈ idealFiniteAdeles L}
      (fun y ↦ ((1 + ‖homeomorphMixedSpace K y.1‖) ^ A)⁻¹) := by
    funext y
    simp only [adeleWeight, Set.indicator_apply, Set.mem_setOf_eq]
  rw [this]
  exact hf.indicator (by rw [hc'.frontier_eq]; simp)
end

end GlobalTheory.CompanionTheory.EpConvB
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSetIntegralOfContinuousUncurry
section
open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Adele2 GroundTheory.Automorphic.GodementSection IdeleGroup

namespace GlobalTheory.CompanionTheory.EisRk1Theta

variable {K : Type*} [Field K] [NumberField K]

theorem continuous_setIntegral_of_continuous_uncurry {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] (ν : Measure Y)
    [IsFiniteMeasureOnCompacts ν] {E : Set Y} (hE : IsCompact (closure E)) (hν : ν E < ⊤)
    {f : X → Y → ℂ} (hf : Continuous (Function.uncurry f)) :
    Continuous fun x ↦ ∫ u in E, f x u ∂ν := by
  have hint : ∀ x, IntegrableOn (f x) E ν := fun x ↦ by
    have hc : Continuous (f x) := hf.comp (Continuous.prodMk_right x)
    exact (hc.continuousOn.integrableOn_compact hE).mono_set subset_closure
  refine continuous_iff_continuousAt.2 fun q ↦ Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  set m := ν.real E with hm
  have hm0 : 0 ≤ m := measureReal_nonneg
  have hδ : 0 < ε / (2 * (m + 1)) := by positivity
  obtain ⟨v, hv, hvu⟩ := hE.mem_uniformity_of_prod (f := f) (s := Set.univ) (q := q)
    hf.continuousOn (Set.mem_univ q) (Metric.dist_mem_uniformity hδ)
  rw [nhdsWithin_univ] at hv
  filter_upwards [hv] with p hp
  rw [dist_eq_norm, ← integral_sub (hint p) (hint q)]
  have hb : ‖∫ u in E, (f p u - f q u) ∂ν‖ ≤ ε / (2 * (m + 1)) * m := by
    refine norm_setIntegral_le_of_norm_le_const hν fun u hu ↦ ?_
    have := hvu p hp u (subset_closure hu)
    rw [Set.mem_setOf_eq, dist_eq_norm] at this
    exact this.le
  refine hb.trans_lt ?_
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
  nlinarith

end GlobalTheory.CompanionTheory.EisRk1Theta
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormsToCechSmulStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.forms_to_cech_smul :
    type_of% @GlobalTheory.CompanionTheory.OmBridge.formToCO_smul :=
  @GlobalTheory.CompanionTheory.OmBridge.formToCO_smul
end

