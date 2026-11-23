module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1925
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0031
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1921
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ShortBoundOfTrivAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1937
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusFormMap

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulIntZSqNonnegOfSqDvd
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open GlobalTheory.CovInt IsDedekindDomain

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

section SqLevPoint
open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt GlobalTheory.PlaceInt.ShortTriv GlobalTheory.IntCuspLat

namespace GlobalTheory.CovInt.SqLev

open GlobalTheory.TorsFac

theorem factor_pow {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    (Xo : Moduli Dw l) (N ℓ : ℕ) (hodd : Odd N) (hMN : l.M ∣ N) (hp : ℓ.Prime) :
    ∃ (k n' Bn j : ℕ) (β : 𝓞 E), ℓ ^ k ∣ l.M ∧ Nat.Coprime n' ℓ ∧
      (N : 𝓞 E) = β * ((ℓ ^ k : ℕ) : 𝓞 E) * n' ∧ β * H.bar β = (Bn : 𝓞 E) ∧ ℓ ^ (2 * k) * Bn = ℓ ^ j ∧
      ∀ (T : Over Xo.X) (t : T ⟶ Xo.univ.t.G), KilledBy Xo l.Mb (t ^ N) →
        t ^ (N ^ 2) = 1 ∧ (t ≫ Xo.univ.t.act.act β) ^ (n' ^ 2 * ℓ ^ (2 * k)) = 1 := by
  have hN : N ≠ 0 := by rintro rfl; exact absurd hodd (by decide)
  have hM : l.M ≠ 0 := by
    intro h
    rw [h] at hMN
    exact hN (zero_dvd_iff.1 hMN)
  obtain ⟨e, n', hn', hNe⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN ℓ hp.ne_one
  obtain ⟨k, m, hm', hMe⟩ := Nat.exists_eq_pow_mul_and_not_dvd hM ℓ hp.ne_one
  have hcop : Nat.Coprime n' ℓ := ((hp.coprime_iff_not_dvd).2 hn').symm
  have hcm : Nat.Coprime m ℓ := ((hp.coprime_iff_not_dvd).2 hm').symm
  have hMN' : ℓ ^ k * m ∣ ℓ ^ e * n' := hNe ▸ hMe ▸ hMN
  have hke : k ≤ e := by
    have h1 : ℓ ^ k ∣ ℓ ^ e * n' := (Dvd.intro _ rfl).trans hMN'
    have h2 : ℓ ^ k ∣ ℓ ^ e := (Nat.Coprime.pow_left k hcop.symm).dvd_of_dvd_mul_right h1
    exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 h2
  obtain ⟨kk, hkk⟩ : m ∣ n' := (hcm.pow_right e).dvd_of_dvd_mul_left ((Dvd.intro_left _ rfl).trans hMN')
  obtain ⟨e', rfl⟩ := Nat.exists_eq_add_of_le hke
  refine ⟨k, n', ℓ ^ (2 * e'), 2 * (k + e'), (ℓ : 𝓞 E) ^ e', ⟨m, hMe⟩, hcop, ?_, ?_, by ring,
    fun T t ht => ⟨?_, ?_⟩⟩
  · rw [hNe]; push_cast; ring
  · rw [map_pow, map_natCast]; push_cast; ring
  · obtain ⟨k2, hk⟩ := hMN
    have := kill Xo t N ht (N : 𝓞 E) (by rw [hk, Nat.cast_mul]; exact l.Mb.mul_mem_right _ (M_mem l))
    rw [← act_nat, ← this]
    congr 2
    push_cast; ring
  · have := kill Xo t N ht ((l.M : 𝓞 E) * kk) (l.Mb.mul_mem_right _ (M_mem l))
    rw [act_pow, ← this]
    congr 2
    rw [hNe, hMe, hkk]; push_cast; ring

section Point
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem class_bound_of_trivAt_pow (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (hst : ∀ a : 𝓞 E, star a = H.bar a)
    (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y) (hC : Good3 C)
    (nab : NabV Xo c) (hnab : IsNab Xo c nab) (e : ℕ) (ρ : ℝ) (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (he : 0 < e)
    (hb : ChBound C e ρ w n) (ℓ : ℕ) (hℓ : ℓ.Prime) (hlu : ¬ IsUnit (ℓ : T.V)) (Λ : GenLat E n) (N : ℕ)
    (hU : Λ.Unimod) (hL : Λ.LevOK N l.M) (P : MvPolynomial (LtN Dw n) c.F) (hP : P ∈ harmL c Λ w)
    (z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G))
    (tp : Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G))
    (F : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n →
      LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo (xOf y))))
    (hz : ∀ i, InZh Xo Λ N (z i)) (hg : GeoInj Xo (xOf y) z) (a : Fin n → Dw.La)
    (htp : ∀ b, tp b ^ N = levPt Xo (xOf y) (a b))
    (hF : ∀ i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N (sOf1 y) (z i b) (tp b) (F i b)) (htr : Λ.TrivAt ℓ) :
    letI := io.toAlgebra
    ((-ρ : ℝ) : EReal) ≤ nval T.V e (((l.M ^ Formalism.L2.Pj.DF Dw w : ℕ) : T.Fr) *
      (io (((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ * ((N : c.F) ^ P.totalDegree)⁻¹) *
        ∑ i, hv Xo c nab y.1 (N ^ 2) (fun b => sqN Xo N (F i b)) P)) := by
  letI := io.toAlgebra
  have hk : ∀ b, KilledBy Xo l.Mb (tp b ^ N) := fun b => by rw [htp b]; exact GlobalTheory.ShortBound.levPt_killed Xo _ _
  obtain ⟨k, n', Bn, j, β₀, hkM, h1, h2, h3, h4, h5⟩ := factor_pow Xo N ℓ hL.1 hL.2.1 hℓ
  have hA : ((ℓ ^ k : ℕ) : 𝓞 E) * H.bar ((ℓ ^ k : ℕ) : 𝓞 E) = ((ℓ ^ (2 * k) : ℕ) : 𝓞 E) := by
    rw [map_natCast]; push_cast; ring
  have key : ∃ u : ℕ, u ∣ l.M ∧ ((-ρ : ℝ) : EReal) ≤ nval T.V e (io (nrm Dw c w (u : 𝓞 E) *
      (((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ * ((N : c.F) ^ P.totalDegree)⁻¹)) *
        ∑ i, hv Xo c nab y.1 (N ^ 2) (fun b => sqN Xo N (F i b)) P) :=
    ⟨ℓ ^ k, hkM, sum_bound_of_trivAt Xo c hst T io y C hC nab hnab e ρ w n he hb ℓ hℓ hlu Λ N l.M hU hL P hP z tp F
      hz hg (fun b => (h5 _ _ (hk b)).1) hF htr n' (ℓ ^ (2 * k)) Bn j _ β₀ h1 h2 hA h3 h4
      (fun b => (h5 _ _ (hk b)).2)⟩
  obtain ⟨u, ⟨m, hm⟩, h⟩ := key
  rw [GlobalTheory.ShortBound.nrm_nat, map_mul, map_pow, map_natCast, _root_.mul_assoc] at h
  rw [hm, mul_pow, Nat.cast_mul, _root_.mul_comm ((u ^ _ : ℕ) : T.Fr), _root_.mul_assoc, nval_mul, Nat.cast_pow u]
  calc ((-ρ : ℝ) : EReal) = 0 + ((-ρ : ℝ) : EReal) := (zero_add _).symm
    _ ≤ _ := add_le_add (nval_natCast_nonneg e _) h

end Point

end GlobalTheory.CovInt.SqLev

end SqLevPoint

section SqLevShort
open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt GlobalTheory.PlaceInt.ShortTriv GlobalTheory.IntCuspLat

namespace GlobalTheory.CovInt.SqLev


open IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions in
theorem smul_nonneg_of_shortRule (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) [StarRing (𝓞 D.host.E)] (hlev : d.IsLev)
    (hnab : IsNab d.Xo₂ d.c₂ d.nab₂)
    (hroot : ∀ (k : Type) [Field k] [Algebra d.c₂.F k] (y₂ : FrPt d.Xo₂ d.c₂ k), evR d.Xo₂ d.c₂ d.cδ y₂ ^ 1 = 1)
    (hwi : ∀ (x0 : Fin n → Dw.La) (q : Fin n → LevQ Dw d.l₂), IsIntegral ℤ (d.w x0 q)) (hM0 : d.l₂.M ≠ 0)
    (Λ : GenLat D.host.E n) (N : ℕ) (hU : Λ.Unimod) (hTM : Λ.TrivAt d.l₂.M) (hN : Λ.LevOK N d.l₂.M)
    (w : (D.host.E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F) (hP : P ∈ harmL c Λ w) (x0 : Fin n → Dw.La)
    (g : Rul Xo c) (hsec : g ∈ sec Xo c w n) (hR : IsShortRule Xo c d Λ N x0 P g) :
    ∀ (la : HeightOneSpectrum (𝓞 c.F)) (ℓ : ℕ), ℓ.Prime → (ℓ : 𝓞 c.F) ∈ la.asIdeal → Λ.TrivAt ℓ →
      ∀ v ∈ valSet Xo c (algCls Xo c) la,
        0 ≤ v ((betaH (Dw := Dw) c Λ * ((GlobalTheory.CovInt.intZ D Dw d.l₂ n w : ℕ) : c.F)) • g) := by
  have hβ : betaH (Dw := Dw) c Λ ≠ 0 := by
    unfold betaH
    split_ifs with h
    · exact h.choose_spec.1
    · exact one_ne_zero
  have hc0 : Nat.card (Fin n → LevQ Dw d.l₂) ≠ 0 := by
    rw [GlobalTheory.PlaceInt.card_fun_levQ]; exact pow_ne_zero _ hM0
  haveI := Nat.finite_of_card_ne_zero hc0
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ, Q = (NumberField.discr D.host.E).natAbs ^ Formalism.L2.Pj.DF Dw w := ⟨_, rfl⟩
  have hZ : GlobalTheory.CovInt.intZ D Dw d.l₂ n w = Nat.card (Fin n → LevQ Dw d.l₂) * (Q * d.l₂.M ^ Formalism.L2.Pj.DF Dw w) := by
    rw [GlobalTheory.CovInt.intZ, hQ, _root_.mul_assoc]
  rw [hZ]
  rintro la ℓ hℓ hmem htr _ ⟨⟨_, Tc, io, e, ho, yI, hy, eta, heta, rfl⟩, rfl⟩
  show 0 ≤ nval Tc.V e (evI yI _)
  obtain ⟨-, ef2, -⟩ := GlobalTheory.PlaceInt.eF_transfer _ _ _ _ Xo c n d Λ
  obtain ⟨T', iT, r, io₂, y₂, C, ζ, z, tp, F, hr, hiT, hfr, hio, hC, hrat, hζ, hz, hgi, htp, hF, hval⟩ :=
    GlobalTheory.PlaceInt.short_value_on_cover _ _ _ _ Xo c n d hlev hnab 1 hroot Λ N hU hTM hN w P hP x0 g hsec hR Tc io yI hy
  haveI : CharZero T'.Fr := algebraRat.charZero _
  have ho' := ho.bc iT hr hiT
  have he' : 0 < r * e := ho'.1
  have hu : ¬ IsUnit (ℓ : T'.V) := fun hu => by
    have h1 := vV_natCast T' hu
    have h2 := ho'.2 (ℓ : c.F)
    rw [map_natCast, h1] at h2
    have h3 := vLa_pos_of_mem la hℓ.ne_zero hmem
    have h4 : (0 : ℤ) < ((r * e : ℕ) : ℤ) := by exact_mod_cast he'
    exact (mul_pos h4 h3).ne h2
  have hch := GlobalTheory.PlaceInt.HostChart.chBound_host D _ Dw _ d.Xo₂ d.c₂ hnab.1 T' io₂ y₂ C (r * e) he' w n _ le_rfl
  have key := fun q => class_bound_of_trivAt_pow d.Xo₂ d.c₂ hnab.1 T' io₂ y₂ C hC _ hnab (r * e) _ w n he' hch ℓ hℓ
      hu Λ N hU hN _ (ef2 _ P hP).1 z (tp q) (F q) hz hgi (fun b => levRep (q b)) (fun b => (htp q b).1) (hF q) htr
  rw [pow_one] at hζ
  rw [← nval_bc iT hr hiT e, evI_smul, map_mul, hval, ← hio, hζ, _root_.one_mul]
  have := Fintype.ofFinite (Fin n → LevQ Dw d.l₂)
  rw [finsum_eq_sum_of_fintype, Finset.mul_sum, Finset.mul_sum]
  refine le_nval_sum T' _ _ _ _ fun q _ => ?_
  have hq := key q
  letI := io₂.toAlgebra
  generalize (∑ i, hv d.Xo₂ d.c₂ d.nab₂ y₂.1 (N ^ 2) (fun b => sqN d.Xo₂ N (F q i b))
    (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P)) = Sm at hq ⊢
  have hb0 : io₂ (d.eF (betaH (Dw := Dw) c Λ)) ≠ 0 := (map_ne_zero io₂).2 ((map_ne_zero d.eF).2 hβ)
  have hc1 : ((Nat.card (Fin n → LevQ Dw d.l₂) : ℕ) : T'.Fr) ≠ 0 := by exact_mod_cast hc0
  have hQ0 : Q ≠ 0 := hQ ▸ pow_ne_zero _ (Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero _))
  have hQ1 : (Q : T'.Fr) ≠ 0 := by exact_mod_cast hQ0
  have hQv : 0 ≤ nval T'.V (r * e) ((Q : T'.Fr) * (((d.l₂.M ^ Formalism.L2.Pj.DF Dw w : ℕ) : T'.Fr) *
      (io₂ (((Λ.mIdx N (Dw.p + Dw.q) : d.c₂.F))⁻¹ *
        ((N : d.c₂.F) ^ (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P).totalDegree)⁻¹) * Sm))) := by
    rw [nval_mul, nval_of_ne hQ1]
    refine le_trans ?_ (add_le_add le_rfl hq)
    rw [← EReal.coe_add, EReal.coe_nonneg, ← sub_eq_add_neg, sub_nonneg, hQ]
    exact GlobalTheory.CovInt.ram_sum_le_vV_discr D.host.E T' _ (fun p hp => Nat.prime_of_mem_primeFactors hp) (r * e) _
  refine le_trans (add_nonneg (GlobalTheory.ShortBound.nval_nonneg (V := T'.V) (r * e) (map_isIntegral_int io₂ (hwi x0 q))) hQv)
    (le_of_eq ?_)
  rw [← nval_mul]
  congr 1
  simp only [map_mul, map_inv₀, map_natCast, Nat.cast_mul]
  generalize (io₂ ((N : d.c₂.F) ^ (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P).totalDegree))⁻¹ = a1
  generalize ((Λ.mIdx N (Dw.p + Dw.q) : ℕ) : T'.Fr)⁻¹ = a2
  field_simp

end GlobalTheory.CovInt.SqLev

end SqLevShort

namespace GlobalTheory.CovInt.SqLev

theorem smul_intZ_sq_nonneg_of_sq_dvd : ∀ (D : D7) (H : Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ)
    (d : DeltaDat Xo c n) [StarRing (𝓞 D.host.E)], d.IsLev → IsNab d.Xo₂ d.c₂ d.nab₂ →
    (∀ (k : Type) [Field k] [Algebra d.c₂.F k] (y₂ : FrPt d.Xo₂ d.c₂ k), evR d.Xo₂ d.c₂ d.cδ y₂ = 1) →
    (∀ (x0 : Fin n → Dw.La) (q : Fin n → LevQ Dw d.l₂), IsIntegral ℤ (d.w x0 q)) → d.l₂.M ≠ 0 →
    ∀ (Λ : GenLat D.host.E n) (N : ℕ), Λ.Unimod → Λ.TrivAt d.l₂.M → Λ.LevOK N d.l₂.M →
    ∀ (w : (D.host.E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmL c Λ w →
    ∀ (x0 : Fin n → Dw.La) (g : Rul Xo c), g ∈ sec Xo c w n → IsShortRule Xo c d Λ N x0 P g →
    ∀ (la : HeightOneSpectrum (𝓞 c.F)) (ℓ : ℕ), ℓ.Prime → (ℓ : 𝓞 c.F) ∈ la.asIdeal → ℓ ^ 2 ∣ d.l₂.M → Λ.TrivAt ℓ →
    ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v ((betaH (Dw := Dw) c Λ * ((intZ D Dw d.l₂ n w ^ 2 : ℕ) : c.F)) • g) := by
  intro D H Dw l Xo c n d _ hlev hnab hroot hwi hM0 Λ N hU hTM hN w P hP x0 g hsec hR la ℓ hℓ hmem _ htr v hv
  have h := smul_nonneg_of_shortRule D H Dw l Xo c n d hlev hnab (fun k _ _ y => by rw [pow_one]; exact hroot k y)
    hwi hM0 Λ N hU hTM hN w P hP x0 g hsec hR la ℓ hℓ hmem htr v hv
  have hV := isVal_valSet (Xo := Xo) (c := c) (cls := algCls Xo c) la v hv
  have hns : ∀ m : ℕ, 0 ≤ v (m • ((betaH (Dw := Dw) c Λ * ((intZ D Dw d.l₂ n w : ℕ) : c.F)) • g)) := by
    intro m
    induction m with
    | zero => rw [zero_smul, hV.zero]; exact le_top
    | succ m ih => rw [succ_nsmul]; exact (le_min ih h).trans (hV.add _ _)
  have e1 : (betaH (Dw := Dw) c Λ * ((intZ D Dw d.l₂ n w ^ 2 : ℕ) : c.F)) • g =
      (intZ D Dw d.l₂ n w) • ((betaH (Dw := Dw) c Λ * ((intZ D Dw d.l₂ n w : ℕ) : c.F)) • g) := by
    rw [← Nat.cast_smul_eq_nsmul c.F, smul_smul]
    congr 1
    push_cast; ring
  rw [e1]
  exact hns _

end GlobalTheory.CovInt.SqLev
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SqLeOfForallNonneg
section
noncomputable section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

namespace GlobalTheory.Poinc.Bdd

theorem sq_le_of_forall_nonneg {A B D : ℤ} (h : ∀ s t : ℤ, 0 ≤ s * s * A + 2 * (s * t) * B + t * t * D) :
    B * B ≤ A * D := by
  have hA : 0 ≤ A := by simpa using h 1 0
  have hD : 0 ≤ D := by simpa using h 0 1
  rcases hA.eq_or_lt with hA0 | hA0
  · subst hA0
    have h2 := h (-B * (D + 1)) 1
    have : B = 0 := by
      by_contra hB
      have hB2 : 1 ≤ B * B := by nlinarith [mul_self_pos.2 hB]
      nlinarith
    subst this; simp
  · have h1 := h B (-A)
    nlinarith

theorem seq_le (F : ℕ → ℤ) (h0 : ∀ k, 0 ≤ F k) (hlc : ∀ k, F (k + 1) * F (k + 1) ≤ F k * F (k + 2)) (d : ℕ)
    (p : ℕ → ℤ) (hd : p d = 1) (hrec : ∑ i ∈ Finset.range (d + 1), p i * F i = 0) :
    F 1 ≤ (∑ i ∈ Finset.range (d + 1), |p i|) * F 0 := by
  set C := ∑ i ∈ Finset.range (d + 1), |p i| with hCdef
  have hC1 : 1 ≤ C := by
    have := Finset.single_le_sum (f := fun i => |p i|) (fun i _ => abs_nonneg (p i)) (Finset.self_mem_range_succ d)
    simpa [hd] using this
  by_contra hlt
  push_neg at hlt
  have hF0 : 0 < F 0 := by
    rcases (h0 0).eq_or_lt with h | h
    · have := hlc 0
      rw [← h] at this hlt
      have h1 : F 1 * F 1 ≤ 0 := by simpa using this
      have : F 1 = 0 := by nlinarith [mul_self_nonneg (F 1)]
      simp [this] at hlt
    · exact h
  have hF1 : C * F 0 < F 1 := hlt
  have key : ∀ k, 0 < F k ∧ F 1 * F k ≤ F 0 * F (k + 1) := by
    intro k
    induction k with
    | zero => exact ⟨hF0, by rw [mul_comm]⟩
    | succ k ih =>
      obtain ⟨hk, hk'⟩ := ih
      have hpos : 0 < F (k + 1) := by
        have : 0 < F 1 * F k := mul_pos (by nlinarith) hk
        nlinarith
      refine ⟨hpos, ?_⟩
      have h2 := hlc k
      have h3 : F 1 * F k * F (k + 1) ≤ F 0 * F (k + 1) * F (k + 1) := mul_le_mul_of_nonneg_right hk' hpos.le
      have h4 : F k * (F 1 * F (k + 1)) ≤ F k * (F 0 * F (k + 2)) := by nlinarith
      exact le_of_mul_le_mul_left h4 hk
  have inc : ∀ k, C * F k < F (k + 1) := by
    intro k
    obtain ⟨hk, hk'⟩ := key k
    have : F 0 * (C * F k) < F 0 * F (k + 1) := by nlinarith
    exact lt_of_mul_lt_mul_left this hF0.le
  have mono : Monotone F := monotone_nat_of_le_succ fun k => by
    have := inc k
    have := (key k).1
    nlinarith
  cases d with
  | zero =>
    simp [hd] at hrec
    exact hF0.ne' hrec
  | succ e =>
    rw [Finset.sum_range_succ, hd, one_mul] at hrec
    rw [Finset.sum_range_succ, hd] at hCdef
    have hle : -(∑ i ∈ Finset.range (e + 1), p i * F i) ≤ (∑ i ∈ Finset.range (e + 1), |p i|) * F e := by
      rw [← Finset.sum_neg_distrib, Finset.sum_mul]
      refine Finset.sum_le_sum fun i hi => ?_
      have hi' : i ≤ e := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      have h1 : -(p i * F i) ≤ |p i| * F i := by
        have := neg_abs_le (p i)
        nlinarith [h0 i]
      exact h1.trans (mul_le_mul_of_nonneg_left (mono hi') (abs_nonneg _))
    have he := inc e
    have hpe := (key e).1
    have : F (e + 1) = -(∑ i ∈ Finset.range (e + 1), p i * F i) := by linarith
    rw [this] at he
    rw [hCdef] at he
    simp only [abs_one] at he
    nlinarith

theorem bddAct_of_isIntegral {O : Type} [CommRing O] (bar : O → O) (hmul : ∀ a b, bar (a * b) = bar a * bar b)
    (hone : bar 1 = 1) (hinv : ∀ a, bar (bar a) = a) (hint : ∀ a : O, IsIntegral ℤ a) : BddAct bar := by
  intro c
  obtain ⟨P, hPm, hP⟩ := hint (bar c * c)
  refine ⟨∑ i ∈ Finset.range (P.natDegree + 1), |P.coeff i|, ?_⟩
  intro X _ _ _ β hβ hpsd x
  have hpow : ∀ k, bar (c ^ k) = bar c ^ k := by
    intro k
    induction k with
    | zero => simpa using hone
    | succ k ih => rw [pow_succ, hmul, ih, pow_succ]
  have hcs : ∀ u v : X, β u v * β u v ≤ β u u * β v v := by
    intro u v
    refine sq_le_of_forall_nonneg fun s t => ?_
    have := hpsd (s • u + t • v)
    simp only [map_add (f := _), map_zsmul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hβ.1 v u] at this
    linarith
  have hF : ∀ k, β (c ^ k • x) (c ^ k • x) = β x ((bar c * c) ^ k • x) := by
    intro k
    rw [hβ.2, smul_smul, hpow, mul_pow]
  set F : ℕ → ℤ := fun k => β (c ^ k • x) (c ^ k • x) with hFdef
  have hlc : ∀ k, F (k + 1) * F (k + 1) ≤ F k * F (k + 2) := by
    intro k
    set y := c ^ k • x
    have e1 : F (k + 1) = β y ((bar c * c) • y) := by
      simp only [hFdef, y, pow_succ', mul_smul]
      rw [hβ.2, smul_smul]
    have e2 : F (k + 2) = β ((bar c * c) • y) ((bar c * c) • y) := by
      have hw : bar (c * c) * (c * c) = bar (bar c * c) * (bar c * c) := by rw [hmul, hmul, hinv]; ring
      show β (c ^ (k + 2) • x) (c ^ (k + 2) • x) = β ((bar c * c) • (c ^ k • x)) ((bar c * c) • (c ^ k • x))
      rw [show c ^ (k + 2) = (c * c) * c ^ k by ring, mul_smul, hβ.2, hβ.2 (bar c * c), smul_smul, smul_smul, hw]
      simp only [mul_smul]
    rw [e1, e2]
    exact hcs _ _
  have hrec : ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * F i = 0 := by
    have h0 : β x ((Polynomial.aeval (bar c * c) P) • x) = 0 := by rw [Polynomial.aeval_def, hP, zero_smul, map_zero]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Polynomial.aeval_eq_sum_range, Finset.sum_smul, map_sum] at h0
    rw [← h0]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hFdef]
    dsimp only
    rw [hF, smul_assoc, map_zsmul, smul_eq_mul]
  have := seq_le F (fun k => hpsd _) hlc P.natDegree P.coeff hPm.coeff_natDegree hrec
  simpa [hFdef] using this

end GlobalTheory.Poinc.Bdd

namespace GlobalTheory.Poinc

open NumberField

theorem bddAct_int_and_cm : BddAct (id : ℤ → ℤ) ∧ ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E), BddAct H.bar := by
  refine ⟨Bdd.bddAct_of_isIntegral id (fun _ _ => rfl) rfl (fun _ => rfl) fun a => Algebra.IsIntegral.isIntegral a, ?_⟩
  intro E _ _ _ H
  refine Bdd.bddAct_of_isIntegral H.bar (fun a b => map_mul _ a b) (map_one _) (fun a => ?_)
    fun a => Algebra.IsIntegral.isIntegral a
  apply RingOfIntegers.ext
  rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]

end GlobalTheory.Poinc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThRuleLower
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

open GlobalTheory.ThetaBound
open Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace GlobalTheory.RefSum.LowP


set_option maxHeartbeats 1000000 in
theorem thRule_lower : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (nab : NabV Xo c), IsNab Xo c nab → ∀ (p : ℕ), p.Prime → ¬ p ∣ l.M → ∀ (la : PointsOfFlagModel.abelian₂ p c) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ P₁ ∈ harmA (Dw := Dw) c a n, ∀ A B : ℝ, PolyBetween Xo la P₁ A B → ∀ (x : Fin n → Dw.La) (f : Rul Xo c), IsThRule Xo c nab x P₁ f → ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e → ∀ y : IntFr Xo c T io, y.IsAlg → (A : EReal) ≤ nval T.V (vV T.V (p : T.Fr)).toNat (evI y f) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro nab hnab p hp hpM la a n P₁ hP₁ A B hPB x f hf T io e ho y hy
  have hM0 : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  obtain ⟨T', iT, r, y', C', ⟨hr, hiT, φ, hφ, hmap⟩, hfin, hgood, hrat⟩ :=
    Prep.exists_good_chart_allRat E H Dw l Xo c hnab.1 T io y hy (l.M ^ 2) (pow_pos hM0 2)
  have ho' := ho.bc iT hr hiT
  have hvp : 0 < vV T.V (p : T.Fr) := by
    have h1 := ho.2 (p : c.F)
    rw [map_natCast] at h1
    rw [h1]
    exact mul_pos (by exact_mod_cast ho.1) (ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam.vLa_pos la.1 p hp.ne_zero la.2)
  have hvp' : vV T'.V (p : T'.Fr) = (r : ℤ) * vV T.V (p : T.Fr) := by
    rw [← map_natCast iT p, hiT]
  obtain ⟨k₀, hk₀⟩ := Int.eq_ofNat_of_zero_le hvp.le
  have he' : (vV T'.V (p : T'.Fr)).toNat = r * (vV T.V (p : T.Fr)).toNat := by
    rw [hvp', hk₀, ← Nat.cast_mul, Int.toNat_natCast, Int.toNat_natCast]
  have hk0 : 0 < k₀ := by omega
  have he'pos : 0 < (vV T'.V (p : T'.Fr)).toNat := by
    rw [he', hk₀, Int.toNat_natCast]; exact Nat.mul_pos hr hk0
  have hu : IsUnit (l.M : T'.V) := by
    refine GlobalTheory.PlaceInt.ShortTriv.isUnit_of_coprime T' (ℓ := p)
      (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 hpM)) fun h => ?_
    have h2 := GlobalTheory.PlaceInt.ShortTriv.vV_natCast T' h
    rw [hvp', hk₀] at h2
    have : (0 : ℤ) < (r : ℤ) * (k₀ : ℤ) := by positivity
    omega
  rw [← nval_bc iT hr hiT ((vV T.V (p : T.Fr)).toNat), ← he']
  obtain ⟨n', j, -, -, a3⟩ := (GlobalTheory.TorsFac.factorisation E H Dw l Xo l.M p l.odd dvd_rfl hp).1 hpM
  letI := (iT.comp io).toAlgebra
  choose F hF using fun b : Fin n =>
    (RatData.exists_thetaVal_data E H Dw l Xo c T'.Fr y'.1).1 hrat (x b)
  have hev : iT (evI y f) = thExpr Xo c nab y'.1 P₁ F := by
    letI : Algebra T.Fr T'.Fr := iT.toAlgebra
    exact GlobalTheory.T.thetaRule_value_integral_framed_point_extension_field E H Dw l Xo c nab hnab T io y T'.Fr φ hφ y'.1 hmap a n x P₁ hP₁ F hF f hf
  have ht : ∀ b, ∃ t' : ptO Xo (xOf y') ⟶ Xo.univ.t.G, t' ^ (l.M ^ 2) = 1 ∧
      IsUUOver Xo.univ.t.G Xo.univ.t.PP l.M (sOf1 y') 1 t' (F b) := by
    intro b
    have h1 : levPt Xo y'.1.x (x b) ^ l.M = 1 := by
      obtain ⟨t', -, -, -, -, b1, b2, -⟩ := hF b
      rw [← b1, ← pow_mul, ← pow_two]
      exact (a3 _ t' (killed_pow Xo t' b2) ⟨2, b2⟩).1
    obtain ⟨t', -, b2, b3⟩ :=
      (uu_through_moves E H Dw l Xo T'.Fr (xOf y') l.M l.odd (sOf1 y')).2 _ _ (F b) h1 (hF b)
    exact ⟨t', (a3 _ t' (killed_pow Xo t' b2) ⟨2, b2⟩).1, b3⟩
  choose t' ht1 ht2 using ht
  have hρ : ∀ k, (A : EReal) ≤ nuLocOf C' (vV T'.V (p : T'.Fr)).toNat k (MvPolynomial.map (iT.comp io) P₁) :=
    fun k => (hPB T' (iT.comp io) (r * e) ho' y' hfin C' k).1
  have hb := GlobalTheory.T.harmonic_value_ge_local_depth_prime_to_p E H Dw l Xo c T' (iT.comp io) y' C' hgood nab hnab _ A a n he'pos P₁ hP₁ hρ l.M l.odd hu
    t' F (fun b => ⟨ht1 b, ht2 b⟩)
  have hh := (hv_linear E H Dw l Xo c hnab.1 nab hnab T'.Fr y'.1 n P₁).2.2 l.M F
  rw [← hh] at hb
  rw [hev, thExpr, map_inv₀, map_pow, map_natCast, GlobalTheory.PlaceInt.TermBound.nval_inv_pow_mul T' _ _ _ hu]
  exact hb

end GlobalTheory.RefSum.LowP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimClosureEqOfIsAlgebraicResidueStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open GlobalTheory.QCoh

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topologicalKrullDim_closure_eq_of_isAlgebraic_residue : ∀ (F : Type) [Field F] (Y X : Scheme.{0}) (π : Y ⟶ X) (sX : X ⟶ Sp F) [LocallyOfFiniteType sX] [LocallyOfFiniteType (π ≫ sX)] (y : Y), (letI := (π.residueFieldMap y).hom.toAlgebra; Algebra.IsAlgebraic (X.residueField (π y)) (Y.residueField y)) → topologicalKrullDim (closure {y} : Set Y) = topologicalKrullDim (closure {π y} : Set X) := by
  first | exact @GlobalTheory.ClosureDim.dim_closure_eq_of_isAlgebraic | exact GlobalTheory.ClosureDim.dim_closure_eq_of_isAlgebraic | (intros; apply GlobalTheory.ClosureDim.dim_closure_eq_of_isAlgebraic <;> assumption)
end

