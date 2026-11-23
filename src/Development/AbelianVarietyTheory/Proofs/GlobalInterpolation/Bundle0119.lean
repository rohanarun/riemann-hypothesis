module

public import Mathlib
public import Formalism.LocalToGlobal.HermitianForms.TiedSym
public import Formalism.LocalToGlobal.GroupLattices.DownNaturalLevelZero
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0013
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Tjcosets
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Formalism.LocalToGlobal.Columns.TiedValLatG
public import Formalism.LocalToGlobal.Columns.CoefModB
public import Formalism.LocalToGlobal.KernelLattices.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClassSumPairingFormsLat
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.BaseEx
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsAnalyticSetupPeriodLatticePair
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CardResidueFieldTotallyRealTypePrime
section
open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace GlobalTheory.SplitResidueCard

theorem absNorm_eq_of_ncard {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime)
    (h : {v : HeightOneSpectrum (𝓞 E) | ((p : ℕ) : 𝓞 E) ∈ v.asIdeal}.ncard = Module.finrank ℚ E)
    {w : Ideal (𝓞 E)} (hwp : w.IsPrime) (hw : ((p : ℕ) : 𝓞 E) ∈ w) :
    Ideal.absNorm w = p := by
  classical
  obtain ⟨hc, -⟩ := Formalism.MainNotions.ModuliIntegralCharts.H1.GSplit.split_of_ncard hp h
  set I : Ideal (𝓞 E) := Ideal.span {((p : ℕ) : 𝓞 E)} with hI
  have hI0 : I ≠ ⊥ := by
    rw [hI, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  set M := UniqueFactorizationMonoid.normalizedFactors I with hM
  have hN : Ideal.absNorm I = p ^ Module.finrank ℚ E := by
    rw [hI, Ideal.absNorm_span_singleton]
    have : ((p : ℕ) : 𝓞 E) = algebraMap ℤ (𝓞 E) (p : ℤ) := by simp
    rw [this, Algebra.norm_algebraMap, RingOfIntegers.rank]
    simp
  have hprod : M.prod = I := Ideal.prod_normalizedFactors_eq_self hI0
  have hge : ∀ P ∈ M, p ≤ Ideal.absNorm P := by
    intro P hP
    obtain ⟨hPp, hIP⟩ := (Ideal.mem_normalizedFactors_iff hI0).1 hP
    have hd : Ideal.absNorm P ∣ p ^ Module.finrank ℚ E := hN ▸ Ideal.absNorm_dvd_absNorm_of_le hIP
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 hd
    have h1 : Ideal.absNorm P ≠ 1 := by rw [Ne, Ideal.absNorm_eq_one_iff]; exact hPp.ne_top
    rw [hj] at h1 ⊢
    exact Nat.le_self_pow (by rintro rfl; simp at h1) p
  have hwM : w ∈ M := (Ideal.mem_normalizedFactors_iff hI0).2
    ⟨hwp, by rw [hI, Ideal.span_singleton_le_iff_mem]; exact hw⟩
  refine le_antisymm ?_ (hge _ hwM)
  obtain ⟨M', hM'⟩ := Multiset.exists_cons_of_mem hwM
  have h2 : p ^ M'.card ≤ (M'.map Ideal.absNorm).prod := by
    have := Multiset.pow_card_le_prod (s := M'.map Ideal.absNorm) (a := p) (fun x hx => by
      obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.1 hx
      exact hge P (hM' ▸ Multiset.mem_cons_of_mem hP))
    simpa using this
  have h3 : Ideal.absNorm w * (M'.map Ideal.absNorm).prod = p * p ^ M'.card := by
    rw [← pow_succ', ← Multiset.card_cons w, ← hM', hc, ← hN, ← hprod, hM', Multiset.prod_cons, map_mul,
      map_multiset_prod]
  by_contra hlt
  push Not at hlt
  have hpos : 0 < p ^ M'.card := pow_pos hp.pos _
  nlinarith

theorem card_quotient_of_ncard {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {p : ℕ} (hp : p.Prime)
    (h : {v : HeightOneSpectrum (𝓞 E) | ((p : ℕ) : 𝓞 E) ∈ v.asIdeal}.ncard = Module.finrank ℚ E)
    (v : HeightOneSpectrum (𝓞 F)) (hv : ((p : ℕ) : 𝓞 F) ∈ v.asIdeal) :
    Nat.card (𝓞 F ⧸ v.asIdeal) = p := by
  have := v.isPrime
  have := v.isMaximal
  obtain ⟨w, hwm, hwo⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  have hw : ((p : ℕ) : 𝓞 E) ∈ w := by
    have h1 : ((p : ℕ) : 𝓞 F) ∈ w.under (𝓞 F) := by rw [← hwo.over]; exact hv
    simpa using (show algebraMap (𝓞 F) (𝓞 E) (p : 𝓞 F) ∈ w from h1)
  have hN : Nat.card (𝓞 E ⧸ w) = p := by
    rw [← absNorm_eq_of_ncard hp h hwm.isPrime hw, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hd : Nat.card (𝓞 F ⧸ v.asIdeal) ∣ p := by
    rw [← hN]
    exact AddSubgroup.card_dvd_of_injective (algebraMap (𝓞 F ⧸ v.asIdeal) (𝓞 E ⧸ w)).toAddMonoidHom
      (FaithfulSMul.algebraMap_injective (𝓞 F ⧸ v.asIdeal) (𝓞 E ⧸ w))
  refine ((Nat.dvd_prime hp).1 hd).resolve_left fun h1 => ?_
  have := (Nat.card_eq_one_iff_unique.1 h1).1
  exact not_subsingleton (𝓞 F ⧸ v.asIdeal) this

theorem card_kv : ∀ (D : D7) (i : Fin 2) (v : HeightOneSpectrum (𝓞 D.host.F)), (D.host.g i : 𝓞 D.host.F) ∈ v.asIdeal → Nat.card (kv D.host.F v) = D.host.g i := by
  intro D i v hv
  rw [← card_quotient_of_ncard (D.host.g_prime i) (D.nd.g_split i) v hv]
  have h := Formalism.UG.P.tjcosets_card_residue v
  rw [h]
  simp [qV, Ideal.absNorm_apply, Submodule.cardQuot_apply]

end GlobalTheory.SplitResidueCard
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ClassPairingIntegralFormRowIsIntegral
section
noncomputable section

namespace GlobalTheory.PairAtClass

open NumberField IsDedekindDomain Formalism.BasicNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 Matrix

section

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι]
  (emb : ι → E →+* K) (σ : K →+* ℂ) {R : Ranks} {I : ChainIn E K ι R} (Q : PerIn I) (hQ : Q.Ok)

theorem petersson_single_left (g w : Q.S'.Cl → GlobalTheory.Mem.Col2.Fr emb σ (R.N R.m - 1) → ℂ) (c : Q.S'.Cl) [DecidableEq Q.S'.Cl] :
    Q.ipP emb σ hQ (fun c' => if c' = c then g c' else 0) w = Q.wt c * ipVal emb σ Q.sgT (g c) (w c) := by
  letI := Q.clFin hQ
  simp only [PerIn.ipP, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  refine (Finset.sum_eq_single c (fun b _ hb => ?_) (fun h => absurd (Finset.mem_univ c) h)).trans ?_
  · simp [hb]
  · simp

theorem petersson_single_right (g w : Q.S'.Cl → GlobalTheory.Mem.Col2.Fr emb σ (R.N R.m - 1) → ℂ) (c : Q.S'.Cl) [DecidableEq Q.S'.Cl] :
    Q.ipP emb σ hQ g (fun c' => if c' = c then w c' else 0) = Q.wt c * ipVal emb σ Q.sgT (g c) (w c) := by
  letI := Q.clFin hQ
  simp only [PerIn.ipP, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  refine (Finset.sum_eq_single c (fun b _ hb => ?_) (fun h => absurd (Finset.mem_univ c) h)).trans ?_
  · simp [hb]
  · simp

theorem period_single (hI : I.Ok) (hc : ι → HCParam R) (G : Q.Mt emb σ)
    (w : Q.S'.Cl → GlobalTheory.Mem.Col2.Fr emb σ (R.N R.m - 1) → ℂ) (c : Q.S'.Cl) [DecidableEq Q.S'.Cl] :
    (Q.per emb σ hI hQ hc).period (fun c' => if c' = c then w c' else 0) G =
      Q.wt c * pairB Q.sgT (polOf (Gr emb σ (R.N R.m - 1)) (shiftOf Q.sgT) (fr0 emb σ (R.N R.m - 1)) (w c))
        (Q.rd emb σ G c) := by
  letI := Q.clFin hQ
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  refine (Finset.sum_eq_single c (fun b _ hb => ?_) (fun h => absurd (Finset.mem_univ c) h)).trans ?_
  · simp [hb]
  · simp

end

theorem pair_integral : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] (emb : ι → E →+* K) (σ : K →+* ℂ) {R : Ranks} {I : ChainIn E K ι R} (Q : PerIn I) (hI : I.Ok) (hQ : Q.Ok) (hc : ι → HCParam R) (hF : (Q.S'.fam emb Q.sgT).Ok) (G : Q.Mt emb σ) (g : Q.S'.Cl → GlobalTheory.Mem.Col2.Fr emb σ (R.N R.m - 1) → ℂ), (∀ w, (Q.per emb σ hI hQ hc).period w G = Q.ipP emb σ hQ g w) → ∀ (c : Q.S'.Cl) [DecidableEq Q.S'.Cl] (y : Formalism.L2.DIV.VV K Q.sgT), y ∈ nabAt emb Q.sgT (Q.S'.Lsh c.1 (Q.S'.rep c)) → Q.rd emb σ G c = MvPolynomial.map σ y.1 → ∀ x ∈ (Q.S'.hlat emb Q.sgT hF).L, ∃ a : 𝓞 K, σ (a : K) = ((Nat.card (Q.S'.Stab c) : ℕ) : ℂ) * Q.ipP emb σ hQ (fun c' => if c' = c then g c' else 0) (fun c' => if c' = c then Q.S'.embF emb σ Q.sgT hF x c' else 0) := by
  intro E K ι _ _ _ _ _ _ _ emb σ R I Q hI hQ hc hF G g hP c _ y hy hG x hx
  have hfin := hQ.step.fin_stab c.1 (Q.S'.rep c)
  have hne : ((Nat.card (Q.S'.Stab c) : ℕ) : ℂ) ≠ 0 := by
    haveI := hfin
    exact_mod_cast Nat.card_pos.ne'
  have hint := ((GlobalTheory.PeriodClassSum.pairBDual E K ι _ emb Q.sgT _ (hQ.step.lsh_full_lat c.1 (Q.S'.rep c)) (x.1 c)).1.1
    (hx c)) y hy
  obtain ⟨a, ha⟩ := hint
  refine ⟨a, ?_⟩
  have e12 : Q.ipP emb σ hQ (fun c' => if c' = c then g c' else 0)
      (fun c' => if c' = c then Q.S'.embF emb σ Q.sgT hF x c' else 0) =
      Q.ipP emb σ hQ g (fun c' => if c' = c then Q.S'.embF emb σ Q.sgT hF x c' else 0) := by
    rw [petersson_single_left, petersson_single_right]
    simp
  rw [e12, ← hP, period_single, hG]
  show _ = _ * (Q.wt c * pairB Q.sgT (polOf (Gr emb σ (R.N R.m - 1)) (shiftOf Q.sgT) (fr0 emb σ (R.N R.m - 1))
    (evV emb (1 : Matrix (Fin (R.N R.m - 1)) (Fin (R.N R.m - 1)) E) Q.sgT σ (x.1 c))) (MvPolynomial.map σ y.1))
  rw [GlobalTheory.PeriodOnStep.polOf_evV, ← GlobalTheory.PeriodOnStep.map_pairB, ← pairBK_apply, PerIn.wt, ← mul_assoc,
    mul_inv_cancel₀ hne, one_mul]
  rw [← ha, LinearMap.toSpanSingleton_apply, Algebra.smul_def, mul_one]

end GlobalTheory.PairAtClass
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ComplexPadicNormKappaSplitPrime
section
noncomputable section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.L2.Ker

namespace GlobalTheory.KapSplitNorm

theorem norm_le_one_of_isIntegral {q : ℕ} [Fact q.Prime] {x : ℂ_[q]} (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  have h1 : IsIntegral (NormedField.valuation (K := ℂ_[q])).integer x := hx.tower_top
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := ℂ_[q]))).mem_of_integral h1
  have h3 : ‖x‖₊ ≤ 1 := h2
  exact_mod_cast h3

theorem norm_natCast_eq_one (q : ℕ) [Fact q.Prime] (n : ℕ) (hn : ¬ q ∣ n) : ‖((n : ℕ) : ℂ_[q])‖ = 1 := by
  have e : ((n : ℕ) : ℂ_[q]) = ((algebraMap ℚ_[q] (PadicAlgCl q) (n : ℚ_[q]) : PadicAlgCl q) : ℂ_[q]) := by simp
  rw [e, PadicComplex.norm_extends']
  exact Padic.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hn)

theorem norm_iota_le_one (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (z : ℂ) (hz : IsIntegral ℤ z) : ‖ι z‖ ≤ 1 :=
  norm_le_one_of_isIntegral (by
    convert map_isIntegral_int (ι : ℂ →+* ℂ_[q]) hz using 1 <;> first | exact Subsingleton.elim _ _ | rfl)

theorem norm_iota_unit (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (n : ℕ) (hn : ¬ q ∣ n) {x w : ℂ} (hx : IsIntegral ℤ x)
    (hw : IsIntegral ℤ w) (hm : (n : ℂ) = x * w) : ‖ι x‖ = 1 := by
  have e1 := norm_iota_le_one q ι x hx
  have e2 := norm_iota_le_one q ι w hw
  have e3 : ‖ι x‖ * ‖ι w‖ = 1 := by
    rw [← norm_mul, ← map_mul, ← hm, map_natCast, norm_natCast_eq_one q n hn]
  refine le_antisymm e1 ?_
  nlinarith [norm_nonneg (ι x), norm_nonneg (ι w)]

theorem norm_rt_eq_one {D : D7} {γ₀ : IsoK D} (k : KapChoice γ₀) (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (p : ℕ)
    (hp : p.Prime) (hs : SplitK D p) (hpq : p ≠ q) : ‖ι (k.rt p)‖ = 1 := by
  have hh := k.rt_pow p hp hs
  obtain ⟨w, hw⟩ : ∃ w : 𝓞 D.host.K, w * k.pi p = (p : 𝓞 D.host.K) ^ classNumber D.host.K := by
    have hmem : (p : 𝓞 D.host.K) ^ classNumber D.host.K ∈ (k.pp p).asIdeal ^ classNumber D.host.K :=
      Ideal.pow_mem_pow (k.pp_over p hp hs) _
    rw [k.pi_gen p hp hs, Ideal.mem_span_singleton'] at hmem
    exact hmem
  have hpq' : ¬ q ∣ p ^ classNumber D.host.K := by
    intro h
    have h1 : q ∣ p := (Fact.out : q.Prime).dvd_of_dvd_pow h
    exact hpq (((Nat.prime_dvd_prime_iff_eq Fact.out hp).1 h1).symm)
  have hwK : (w : D.host.K) * (k.pi p : D.host.K) = ((p ^ classNumber D.host.K : ℕ) : D.host.K) := by
    have := congrArg (algebraMap (𝓞 D.host.K) D.host.K) hw
    simpa using this
  let fK : D.host.K →+* ℂ := D.host.φ₀.comp (algebraMap D.host.K D.host.E)
  let fK' : D.host.K →+* ℂ := D.host.φ₀.comp ((D.host.conj : D.host.E →+* D.host.E).comp (algebraMap D.host.K D.host.E))
  have hint : ∀ (g : D.host.K →+* ℂ) (x : 𝓞 D.host.K), IsIntegral ℤ (g (x : D.host.K)) := fun g x =>
    map_isIntegral_int g (NumberField.RingOfIntegers.isIntegral_coe x)
  have e : ∀ g : D.host.K →+* ℂ, ((p ^ classNumber D.host.K : ℕ) : ℂ) = g (k.pi p : D.host.K) * g (w : D.host.K) := by
    intro g
    rw [← map_natCast g, ← hwK, map_mul, mul_comm]
  have h1 : ‖ι (D.host.φ₀ (((k.pi p : 𝓞 D.host.K) : D.host.K) : D.host.E))‖ = 1 :=
    norm_iota_unit q ι _ hpq' (hint fK (k.pi p)) (hint fK w) (e fK)
  have h2 : ‖ι (D.host.φ₀ (D.host.conj (((k.pi p : 𝓞 D.host.K) : D.host.K) : D.host.E)))‖ = 1 :=
    norm_iota_unit q ι _ hpq' (hint fK' (k.pi p)) (hint fK' w) (e fK')
  have hpow : ‖ι (k.rt p)‖ ^ (2 * classNumber D.host.K) = 1 := by
    rw [← norm_pow, ← map_pow, hh, map_div₀, norm_div, h1, h2, div_one]
  have hc := NumberField.classNumber_pos D.host.K
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by omega)).1 hpow

theorem norm_kappa_split : ∀ (D : D7) (γ₀ : IsoK D) (k : KapChoice γ₀) (q : ℕ) [Fact q.Prime], SplitK D q →
    ∀ ι : ℂ ≃+* ℂ_[q], ‖ι k.kappa‖ = ‖ι (k.rt q)‖ ^ (-(k.yP q)) := by
  intro D γ₀ k q _ hsq ι
  have hfin := yFinite D γ₀ k
  have hfinS : (Function.mulSupport
      (fun p : {p : ℕ // p.Prime ∧ SplitK D p} => k.rt p ^ (-(k.yP p)))).Finite := by
    refine (hfin.preimage Subtype.val_injective.injOn).subset ?_
    intro p hp
    refine ⟨p.2.1, p.2.2, ?_⟩
    intro h0
    apply hp
    simp [h0]
  let F : ℂ →* ℝ :=
    { toFun := fun z => ‖ι z‖
      map_one' := by simp
      map_mul' := fun x y => by simp [norm_mul] }
  have hF : ∀ z, F z = ‖ι z‖ := fun _ => rfl
  rw [KapChoice.kappa, ← hF, MonoidHom.map_finprod F hfinS,
    finprod_eq_single _ (⟨q, Fact.out, hsq⟩ : {p : ℕ // p.Prime ∧ SplitK D p})]
  · rw [hF, map_zpow₀, norm_zpow]
  · intro p hp
    have hpq : (p : ℕ) ≠ q := fun h => hp (Subtype.ext h)
    rw [hF, map_zpow₀, norm_zpow, norm_rt_eq_one k q ι p p.2.1 p.2.2 hpq, one_zpow]

end GlobalTheory.KapSplitNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ConjugateEmbeddingsInduceDifferentPrimesSplit
section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.L2.Ker

noncomputable section

namespace GlobalTheory.ConjPlace

theorem norm_le_one_of_isIntegral {q : ℕ} [Fact q.Prime] {x : ℂ_[q]} (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  have h1 : IsIntegral (NormedField.valuation (K := ℂ_[q])).integer x := hx.tower_top
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := ℂ_[q]))).mem_of_integral h1
  have h3 : ‖x‖₊ ≤ 1 := h2
  exact_mod_cast h3

theorem norm_le_one_of_int {q : ℕ} [Fact q.Prime] {K : Type} [Field K] (j : K →+* ℂ_[q]) (y : 𝓞 K) :
    ‖j (y : K)‖ ≤ 1 :=
  norm_le_one_of_isIntegral (by convert map_isIntegral_int j (RingOfIntegers.isIntegral_coe y); exact Subsingleton.elim _ _)

theorem norm_intCast_eq (q : ℕ) [Fact q.Prime] (n : ℤ) : ‖((n : ℤ) : ℂ_[q])‖ = ‖((n : ℤ) : ℚ_[q])‖ := by
  have e : ((n : ℤ) : ℂ_[q]) = algebraMap ℚ_[q] ℂ_[q] ((n : ℤ) : ℚ_[q]) := (map_intCast _ n).symm
  rw [e]
  exact PadicComplex.norm_extends' (p := q) _

theorem norm_intCast_lt_one_iff (q : ℕ) [Fact q.Prime] (n : ℤ) : ‖((n : ℤ) : ℂ_[q])‖ < 1 ↔ (q : ℤ) ∣ n := by
  rw [norm_intCast_eq]
  exact Padic.norm_intCast_lt_one_iff

theorem exists_sq_add (q : ℕ) [Fact q.Prime] (d : ℕ) (h : jacobiSym (-(d : ℤ)) q = 1) :
    ¬ (q : ℤ) ∣ d ∧ ∃ t : ℤ, (q : ℤ) ∣ t ^ 2 + d := by
  have hl : legendreSym q (-(d : ℤ)) = 1 := by rw [jacobiSym.legendreSym.to_jacobiSym]; exact h
  have h0 : ((-(d : ℤ) : ℤ) : ZMod q) ≠ 0 := by
    intro h0
    rw [(legendreSym.eq_zero_iff q _).2 h0] at hl
    exact zero_ne_one hl
  obtain ⟨r, hr⟩ := (legendreSym.eq_one_iff q h0).1 hl
  refine ⟨?_, ⟨(r.val : ℤ), ?_⟩⟩
  · intro hd
    apply h0
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (dvd_neg.2 hd)
  · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast at hr ⊢
    rw [ZMod.natCast_zmod_val]
    linear_combination (-1 : ZMod q) * hr

theorem exists_small_not_conj {E : Type} [Field E] [CharZero E] (K : IntermediateField ℚ E) (φ : E →+* ℂ) (c : E ≃ₐ[ℚ] E)
    (d q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) (hj : jacobiSym (-(d : ℤ)) q = 1) (ι : ℂ ≃+* ℂ_[q])
    (s : K) (hs : s * s = -(d : K)) (hc : c (algebraMap K E s) = -algebraMap K E s) :
    ∃ y : 𝓞 K, ‖ι (φ ((y : K) : E))‖ < 1 ∧ 1 ≤ ‖ι (φ (c ((y : K) : E)))‖ := by
  obtain ⟨hnd, t, ht⟩ := exists_sq_add q d hj
  have hint : IsIntegral ℤ s :=
    ⟨Polynomial.X ^ 2 + Polynomial.C (d : ℤ), Polynomial.monic_X_pow_add_C _ two_ne_zero, by simp [sq, hs]⟩
  let B : 𝓞 K := ⟨s, hint⟩
  let j : E →+* ℂ_[q] := ι.toRingHom.comp φ
  let jK : K →+* ℂ_[q] := j.comp (algebraMap K E)
  have hc' : c (s : E) = -(s : E) := hc
  have hsE : (s : E) * (s : E) = -(d : E) := by
    have := congrArg (fun x : K => (x : E)) hs
    simpa using this
  have hcoe : ∀ u : ℤ, (((B + u : 𝓞 K) : K) : E) = (s : E) + (u : E) := by
    intro u; push_cast; rfl
  have hle : ∀ y : 𝓞 K, ‖j ((y : K) : E)‖ ≤ 1 := fun y => norm_le_one_of_int jK y

  have hodd : ∀ u : ℤ, (q : ℤ) ∣ 2 * u → (q : ℤ) ∣ u := by
    intro u h
    rcases (Nat.prime_iff_prime_int.mp (Fact.out : q.Prime)).dvd_or_dvd h with h2 | h2
    · exfalso
      have : q ∣ 2 := by exact_mod_cast h2
      exact hq2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 this)
    · exact h2
  have key : ∀ u : ℤ, (u = t ∨ u = -t) → ‖j (((B + u : 𝓞 K) : K) : E)‖ < 1 →
      1 ≤ ‖j (c (((B + u : 𝓞 K) : K) : E))‖ := by
    intro u hu h1
    by_contra h2
    push_neg at h2
    have e2 : c (((B + u : 𝓞 K) : K) : E) = -(s : E) + (u : E) := by
      rw [hcoe, map_add (f := _), map_intCast, hc']
    have hsum : j (((B + u : 𝓞 K) : K) : E) + j (c (((B + u : 𝓞 K) : K) : E)) = (((2 * u : ℤ)) : ℂ_[q]) := by
      rw [e2, hcoe, ← map_add (f := _)]
      have : (s : E) + (u : E) + (-(s : E) + (u : E)) = ((2 * u : ℤ) : E) := by push_cast; ring
      rw [this, map_intCast]
    have hlt : ‖(((2 * u : ℤ)) : ℂ_[q])‖ < 1 := by
      rw [← hsum]
      exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt h1 h2)
    have hdu : (q : ℤ) ∣ u := hodd u ((norm_intCast_lt_one_iff q _).1 hlt)
    have hdt : (q : ℤ) ∣ t := by
      rcases hu with rfl | rfl
      · exact hdu
      · exact dvd_neg.1 hdu
    exact hnd ((dvd_add_right (dvd_pow hdt two_ne_zero)).1 ht)
  have hprod : j (((B + t : 𝓞 K) : K) : E) * j (((B + (-t : ℤ) : 𝓞 K) : K) : E) = ((-(t ^ 2 + d) : ℤ) : ℂ_[q]) := by
    rw [← map_mul, hcoe, hcoe]
    have : ((s : E) + (t : E)) * ((s : E) + ((-t : ℤ) : E)) = ((-(t ^ 2 + d) : ℤ) : E) := by
      push_cast
      linear_combination hsE
    rw [this, map_intCast]
  have hpl : ‖((-(t ^ 2 + d) : ℤ) : ℂ_[q])‖ < 1 := (norm_intCast_lt_one_iff q _).2 (dvd_neg.2 ht)
  by_cases h1 : ‖j (((B + t : 𝓞 K) : K) : E)‖ < 1
  · exact ⟨B + t, h1, key t (Or.inl rfl) h1⟩
  · push_neg at h1
    have h2 : ‖j (((B + (-t : ℤ) : 𝓞 K) : K) : E)‖ < 1 := by
      by_contra h2
      push_neg at h2
      rw [← hprod, norm_mul] at hpl
      nlinarith
    exact ⟨B + (-t : ℤ), h2, key (-t) (Or.inr rfl) h2⟩

theorem conj_place_ne : ∀ (D : D7) (q : ℕ) [Fact q.Prime], q ≠ 2 → jacobiSym (-(D.host.d : ℤ)) q = 1 →
    ∀ ι : ℂ ≃+* ℂ_[q], ∃ y : 𝓞 D.host.K, ‖ι (D.host.φ₀ ((y : D.host.K) : D.host.E))‖ < 1 ∧
      1 ≤ ‖ι (D.host.φ₀ (D.host.conj ((y : D.host.K) : D.host.E)))‖ := by
  intro D q _ hq2 hj ι
  obtain ⟨s, h1, h2⟩ := sqrtInK D
  exact exists_small_not_conj D.host.K D.host.φ₀ D.host.conj D.host.d q hq2 hj ι s h1 h2

end GlobalTheory.ConjPlace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsAnalyticSetupPeriodLatticePairStatement
section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_analyticSetup_periodLatticePair : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → ∃ (g : ℕ) (S : JMB.Setup g) (e : VC D N N' ≃L[ℂ] (Fin g → ℂ)), S.d = D.host.d ∧ S.Ok ∧ (∀ x, e x ∈ S.La ↔ x ∈ La D B.tor L L') ∧ (∀ x y, JMB.hf S.Hm (e x) (e y) = Hf D B.tor x y) ∧ (∀ x y : Matrix (Fin N') (Fin N) D.host.E, JMB.beta S.d S.Hm (e (δ • embV D B.tor x)) (e (δ • embV D B.tor y)) = D.host.φ₀ ((hYY D x y : D.host.K) : D.host.E) / (Ideal.absNorm cc : ℂ)) ∧ (∀ x ∈ La D B.tor L L', ∃ (n : ℕ) (A : Matrix (Fin N') (Fin N) D.host.E), 0 < n ∧ x = δ • embV D B.tor A ∧ (n : D.host.E) • A ∈ YYl D L L') ∧ ∀ (q r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), Nat.Coprime (Ideal.absNorm cc) q → NNBasis D B.tor δ q L L' b → S.NNBasis q fun i => e (δ • embV D B.tor (b i)) := by
  first | exact @GlobalTheory.MomSetup.periodSetup | exact GlobalTheory.MomSetup.periodSetup | (intros; apply GlobalTheory.MomSetup.periodSetup <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GLevHChiPowEqOneAndMemRange
section
open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace GlobalTheory

theorem gLevH_chi_pow_eq_one_and_mem_range : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (S : StepLevel F E σ J T f bad) (gp : Fin 2 → ℕ) (G : GLoc F E σ gp) (H : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp a : 𝓞 F) ∈ v.asIdeal → Subgroup (GL (Fin n) (kv F v))) (lam : ∀ a v h, H a v h →* ℂˣ) (_ : GLevH S G H lam) (K : Type) [Field K] (s : K →+* ℂ) (N : ℕ), (∀ i, (gp i).Prime) → (∀ a v h M, ((lam a v h M : ℂˣ) : ℂ) ^ N = 1 ∧ ∃ r : K, s r = ((lam a v h M : ℂˣ) : ℂ)) → ∀ x : S.U, ((S.chi x : ℂˣ) : ℂ) ^ N = 1 ∧ ∃ r : K, s r = ((S.chi x : ℂˣ) : ℂ) := by
  intro F E _ _ _ _ _ σ n J T f bad S gp G H lam L K _ s N _ hl x
  have hmul : ∀ a b : ℂ, (a ^ N = 1 ∧ ∃ r : K, s r = a) → (b ^ N = 1 ∧ ∃ r : K, s r = b) →
      ((a * b) ^ N = 1 ∧ ∃ r : K, s r = a * b) := by
    rintro a b ⟨ha, r, hr⟩ ⟨hb, r', hr'⟩
    exact ⟨by rw [mul_pow, ha, hb, one_mul], r * r', by rw [map_mul, hr, hr']⟩
  have hone : (1 : ℂ) ^ N = 1 ∧ ∃ r : K, s r = 1 := ⟨one_pow N, 1, map_one s⟩
  rw [L.chi_eq x]
  refine Finset.prod_induction _ (fun z : ℂ => z ^ N = 1 ∧ ∃ r : K, s r = z) hmul hone ?_
  intro a _
  refine finprod_induction (fun z : ℂ => z ^ N = 1 ∧ ∃ r : K, s r = z) hone hmul ?_
  intro v
  refine finprod_induction (fun z : ℂ => z ^ N = 1 ∧ ∃ r : K, s r = z) hone hmul ?_
  intro h
  obtain ⟨h1, r, hr⟩ := hl a v h (L.red a v h x)
  exact ⟨by rw [inv_pow, h1, inv_one], r⁻¹, by rw [map_inv₀, hr]⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LamJMemRangeAndPowEqOne
section
open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace GlobalTheory

theorem lamJ_mem_range_and_pow_eq_one :
    ∀ (k K : Type) [Field k] [Field K] (s : K →+* ℂ) (p : ℕ), p.Prime → Nat.card k = p →
      (∃ ζ : K, IsPrimitiveRoot ζ p) → (∃ ζ : K, IsPrimitiveRoot ζ (p - 1)) →
      ∀ (n : ℕ) (ψ : AddChar k ℂ) (χ : ℕ → MulChar k ℂ) (a t nb skip : ℕ)
        (M : Matrix (Fin n) (Fin n) k),
        (∃ r : K, s r = lamJ ψ χ a t nb skip M) ∧
          (lamJ ψ χ a t nb skip M ≠ 0 → lamJ ψ χ a t nb skip M ^ (p * (p - 1)) = 1) := by
  intro k K _ _ s p hp hk ⟨ζ, hζ⟩ ⟨ξ, hξ⟩ n ψ χ a t nb skip M
  haveI : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; exact hp.ne_zero)
  letI : Fintype k := Fintype.ofFinite k
  have hk' : Fintype.card k = p := by rw [← Nat.card_eq_fintype_card]; exact hk
  have hψ : ∀ x : k, ψ x ^ p = 1 := by
    intro x
    rw [← AddChar.map_nsmul_eq_pow, ← hk, card_nsmul_eq_zero', AddChar.map_zero_eq_one]
  have hχ : ∀ (i : ℕ) (x : k), χ i x ≠ 0 → χ i x ^ (p - 1) = 1 := by
    intro i x hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hx (MulChar.map_zero _)
    rw [← map_pow, ← hk', FiniteField.pow_card_sub_one_eq_one x hx0, map_one]
  have hp1 : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
  have hψr : ∀ x : k, ψ x ∈ s.range := fun x =>
    complex_rootOfUnity_mem_range_of_isPrimitiveRoot K s p ζ hp.pos hζ _ (hψ x)
  have hχr : ∀ (i : ℕ) (x : k), χ i x ∈ s.range := by
    intro i x
    by_cases hx : χ i x = 0
    · rw [hx]; exact zero_mem _
    · exact complex_rootOfUnity_mem_range_of_isPrimitiveRoot K s (p - 1) ξ hp1 hξ _ (hχ i x hx)
  unfold lamJ
  refine ⟨?_, ?_⟩
  · exact mul_mem (hψr _) (prod_mem fun i _ => hχr i _)
  · intro h
    have h2 := Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul h)
    rw [mul_pow, pow_mul, hψ, one_pow, one_mul, mul_comm p, pow_mul, ← Finset.prod_pow,
      Finset.prod_eq_one (fun i hi => hχ i _ (h2 i hi)), one_pow]

end GlobalTheory
end

