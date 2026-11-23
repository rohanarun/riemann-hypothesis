module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0049
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CardStabilizerForgetFr
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0053
public import Formalism.LocalToGlobal.Columns.PolyFnLemmas
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0108
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemMulLatIff

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClassSumPairingOfIsFormsOf
section
noncomputable section

namespace GlobalTheory.PeriodOnStep

open NumberField IsDedekindDomain Module Formalism.BasicNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.DivisionValues
open GlobalTheory.IndefiniteRowSideFullHecke
open GlobalTheory.PeriodClassSum GlobalTheory.Mem.Col2
open scoped Matrix ComplexOrder

section Step

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs)

theorem Lsh_eq_N {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {SG : Finset (HeightOneSpectrum (𝓞 E))}
    (d : DecoSet (E := E) (n := n) (ST := ∅) (SG := SG)) : d.1.Lsh = d.1.N := by
  have e : d.1.L = d.1.N := by
    rw [Deco.L]
    simp
  rw [Deco.Lsh, e]
  exact d.2.uni

theorem emb_mem_cmMax (hX : X.Ok) (τ : X.Tau) (x : X.E) : X.emb τ x ∈ cmMax X.K := fun φ => by
  rw [← hX.emb_star]
  exact hX.conjE (φ.comp (X.emb τ)) x

theorem root_mem_cmMax (hX : X.Ok) {c : X.K} (hc : ∃ m : ℕ, 0 < m ∧ c ^ m = 1) : c ∈ cmMax X.K := fun φ => by
  obtain ⟨m, hm, hc⟩ := hc
  have h1 := star_mul_root hX.conjK hm hc
  have h2 : star (φ c) * φ c = 1 := by
    have h3 : ‖φ c‖ = 1 := Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hc, map_one]) hm.ne'
    rw [← starRingEnd_apply, Complex.conj_mul', h3]
    simp
  have h0 : φ c ≠ 0 := right_ne_zero_of_mul_eq_one h2
  refine mul_right_cancel₀ h0 ?_
  rw [← map_mul, h1, map_one, starRingEnd_apply, h2]

theorem row_act_rat (hX : X.Ok) (g : (mtildeGSD W Ch sel mu P).G) (i j) :
    (mtildeGSD W Ch sel mu P).bV.repr ((mtildeGSD W Ch sel mu P).ρ g ((mtildeGSD W Ch sel mu P).bV j)) i ∈ cmMax X.K := by
  rw [formGSD_rho, map_smul, Finsupp.smul_apply, smul_eq_mul]
  exact mul_mem (root_mem_cmMax hX (LevFam.chr_root _ _))
    (coefAction_repr_mem_subfield X.emb _ W.sgTrue (emb_mem_cmMax hX) _ i j).1

theorem isFormsOf_MtildeH (hX : X.Ok) : IsFormsOf _ (mtildeOk W Ch sel mu hX P) (MtildeL W Ch sel mu P)
    (MtildeH W Ch hX sel mu P) (LinearEquiv.refl _ _) :=
  isFormsOf_toH _ _ (row_act_rat W Ch sel mu P hX) (fun v => by rw [row_gramV]; exact gramB_posDef _ _) _

def rowPt (c : (stepX Ch sel mu P).Cl) : RowPt Pr R sel mu := toRow sel mu ((stepX Ch sel mu P).rep c).1.1

def rowCl (c : (stepX Ch sel mu P).Cl) : (mtildeGSD W Ch sel mu P).Cl := (mtildeGSD W Ch sel mu P).cls (rowPt Ch sel mu P c)

theorem rowCl_surjective : Function.Surjective (rowCl W Ch sel mu P) := by
  rintro ⟨d⟩
  obtain ⟨p, rfl⟩ := toRow_surjective sel mu d
  refine ⟨(stepX Ch sel mu P).cl () (trivPt X _ _ _ _ p), ?_⟩
  obtain ⟨g, hg⟩ := (stepX Ch sel mu P).exists_mv () (trivPt X _ _ _ _ p)
  have h1 := congrArg (fun q => toRow sel mu q.1.1) hg
  refine Eq.symm (((mtildeGSD W Ch sel mu P).cls_eq_iff _ _).2 ⟨toRowG Ch sel mu P g, ?_⟩)
  exact (toRow_smul Ch sel mu P g _).symm.trans h1

variable (hd : Disjoint Pr.vGs (QE sel (mu : Chr X.F X.E X.K)))


include hd in
theorem exists_step_smul (a : FormG (rowTy Ch sel mu P).inv) (p q : (stepX Ch sel mu P).D ())
    (h : a • toRow sel mu p.1.1 = toRow sel mu q.1.1) :
    ∃ g : (stepX Ch sel mu P).G (), toRowG Ch sel mu P g = a ∧ (letI := (stepX Ch sel mu P).actD (); g • p) = q := by
  obtain ⟨g, h1, h2⟩ := exists_toRowG_smul Ch sel mu P hd a _ _ h
  refine ⟨g, h1, (trivPt X _ _ _ _).symm.injective h2⟩

include hd in
theorem rowCl_injective : Function.Injective (rowCl W Ch sel mu P) := by
  rintro ⟨⟨⟩, c⟩ ⟨⟨⟩, c'⟩ h
  obtain ⟨a, ha⟩ := ((mtildeGSD W Ch sel mu P).cls_eq_iff _ _).1 h
  obtain ⟨g, -, hg⟩ := exists_step_smul Ch sel mu P hd a _ _ ha
  refine congrArg (Sigma.mk ()) ?_
  rw [← (stepX Ch sel mu P).rp_spec () c, ← (stepX Ch sel mu P).rp_spec () c']
  exact Quotient.sound ⟨g, hg⟩

def clEquiv : (stepX Ch sel mu P).Cl ≃ (mtildeGSD W Ch sel mu P).Cl :=
  Equiv.ofBijective _ ⟨rowCl_injective W Ch sel mu P hd, rowCl_surjective W Ch sel mu P⟩


include hd in
theorem card_stab (c : (stepX Ch sel mu P).Cl) : Nat.card ((stepX Ch sel mu P).Stab c) =
    Nat.card (MulAction.stabilizer (mtildeGSD W Ch sel mu P).G (rowPt Ch sel mu P c)) := by
  refine Eq.trans ?_ (card_stabilizer_toRow Ch sel mu P hd _)
  refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl _) fun g => ?_)
  exact (trivPt X _ _ _ _).symm.injective.eq_iff.symm


variable (hF : ((stepX Ch sel mu P).fam X.emb W.sgTrue).Ok)

end Step

section Lattice

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs) (hd : Disjoint Pr.vGs (QE sel (mu : Chr X.F X.E X.K)))
  (hF : ((stepX Ch sel mu P).fam X.emb W.sgTrue).Ok) (h' : (dualGSD W Ch sel mu P).Ok)

end Lattice

section Pol

variable {K : Type} [Field K] (σ : K →+* ℂ)

theorem map_fockB {τ : Type} (f g : MvPolynomial τ K) : σ (fockB f g) = fockB (MvPolynomial.map σ f) (MvPolynomial.map σ g) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [fockB_eq_sum _ _ f.support (MvPolynomial.support_map_subset _ _), fockB, map_sum]
  exact Finset.sum_congr rfl fun m _ => by rw [map_mul, map_mul, map_natCast, MvPolynomial.coeff_map, MvPolynomial.coeff_map]

theorem map_pairB {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (F F' : Pol K ι n) :
    σ (pairB lam F F') = pairB lam (MvPolynomial.map σ F) (MvPolynomial.map σ F') := by
  rw [pairB_apply, pairB_apply, map_mul, map_inv₀, map_fockB, extNormB, extNormB, map_prod]
  congr 2
  exact Finset.prod_congr rfl fun τ _ => by rw [map_fockB, Formalism.L2.DIV.map_extremal]

theorem polOf_evV {E ι : Type} [Field E] [Fintype ι] {n : ℕ} (emb : ι → E →+* K) (lam : ι → DomWeight n) (x : VV K lam) :
    polOf (Gr emb σ n) (Formalism.L2.Forms.shiftOf lam) (fr0 emb σ n) (evV emb 1 lam σ x) = MvPolynomial.map σ x.1 := by
  have e : (fun τ => ((fr0 emb σ n).1 τ)⁻¹) = 1 := funext fun _ => inv_one
  rw [evV_apply, ← e, polOf_fnOf]

end Pol

section Layer

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs) {I : ChainIn X.E X.K X.Tau R} (b0 : (I.S R.m).β)
  (til : ∀ b, (stepX Ch sel mu P).D b → (I.S R.m).D b0) (ext : ∀ b, (stepX Ch sel mu P).G b →* (I.S R.m).G b0)
  (tz : X.E) (H : ∀ b, Subgroup ((stepX Ch sel mu P).G b))

@[reducible] def perOn : PerIn I where
  S' := stepX Ch sel mu P
  b0 := b0
  til := til
  ext := ext
  sg := W.sgW
  tz := tz
  H := H

variable (hd : Disjoint Pr.vGs (QE sel (mu : Chr X.F X.E X.K))) (σ : X.K →+* ℂ)


include hd in
theorem row_law (z : (mtildeGSD W Ch sel mu P).EqFun) (g : (stepX Ch sel mu P).G ()) (d : (stepX Ch sel mu P).D ()) :
    MvPolynomial.map σ (z.1 (toRow sel mu (letI := (stepX Ch sel mu P).actD (); g • d : (stepX Ch sel mu P).D ()).1.1)).1 =
      (σ ((stepX Ch sel mu P).chr () g : X.K))⁻¹ • rhoP W.sgTrue (embGL (embAt σ X.emb) ((stepX Ch sel mu P).gam () g))
        (MvPolynomial.map σ (z.1 (toRow sel mu d.1.1)).1) := by
  have h1 := z.2 (toRowG Ch sel mu P g) (toRow sel mu d.1.1)
  rw [mtilde_rho_toRowG W Ch sel mu P hd] at h1
  have h2 := (congrArg z.1 (toRow_smul Ch sel mu P g d.1.1)).trans h1
  refine (congrArg (fun y : VV X.K W.sgTrue => mapS σ y.1) h2).trans ?_
  refine (LinearMap.map_smulₛₗ (mapS σ) _ (actP W.sgTrue (embGL X.emb (ufGL _ _ g.1)) (z.1 (toRow sel mu d.1.1)).1)).trans ?_
  rw [Units.val_inv_eq_inv_val, map_inv₀, mapS_apply, GlobalTheory.ValCmp.use₂]
  congr 1

def rowEmb : (mtildeGSD W Ch sel mu P).EqFun →ₛₗ[σ] (perOn W Ch sel mu P b0 til ext tz H).Mt X.emb σ where
  toFun z := ⟨fun _ d => MvPolynomial.map σ (z.1 (toRow sel mu d.1.1)).1, fun _ d =>
    ⟨GlobalTheory.Proof.TensorMapDescent.map_mem_VV σ W.sgTrue _ (z.1 (toRow sel mu d.1.1)).2, fun g _ => row_law W Ch sel mu P hd σ z g d⟩⟩
  map_add' _ _ := Subtype.ext (funext fun _ => funext fun _ => map_add (mapS σ) _ _)
  map_smul' _ _ := Subtype.ext (funext fun _ => funext fun _ => LinearMap.map_smulₛₗ (mapS σ) _ _)

variable (hX : X.Ok) (hc : X.Tau → HCParam R)
  {Pl : Rows.Places X.K} (J : AtIn I) (Z : FmIn J Pl) (hI : I.Ok) (hJ : J.Ok)
  (hQ : (perOn W Ch sel mu P b0 til ext tz H).Ok) (l : J.Laws X.emb σ hc)
  (lf : FmLaws J (perOn W Ch sel mu P b0 til ext tz H) X.emb σ hc Pl hI hQ)
  (hT : (perOn W Ch sel mu P b0 til ext tz H).Over J)

section AnyLattice

variable {Λ' : HLat X.K} {ι : Λ'.V ≃ₗ[X.K] (mtildeGSD W Ch sel mu P).EqFun}
  (hι : IsFormsOf _ (mtildeOk W Ch sel mu hX P) (MtildeL W Ch sel mu P) Λ' ι)

include hι

end AnyLattice

end Layer

end GlobalTheory.PeriodOnStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsUnramifiedAtOfIsSplitAt
section
open NumberField IsDedekindDomain GlobalTheory.UnitaryBC

namespace GlobalTheory.SplitUnram


set_option maxHeartbeats 800000 in
theorem isUnramifiedAt_of_isSplitAt : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L]
    (w : HeightOneSpectrum (𝓞 L)), IsSplitAt w →
    Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield L)) w.asIdeal := by
  intro L _ _ _ w hw
  obtain ⟨u, hne, hu⟩ := hw
  set K := maximalRealSubfield L
  set p : Ideal (𝓞 K) := w.asIdeal.under (𝓞 K) with hpdef
  have hup : u.asIdeal.under (𝓞 K) = p := by
    have := congrArg HeightOneSpectrum.asIdeal hu
    exact this
  haveI : w.asIdeal.LiesOver p := ⟨rfl⟩
  haveI : u.asIdeal.LiesOver p := ⟨hup.symm⟩
  have hp0 : p ≠ ⊥ := (w.under (𝓞 K)).ne_bot
  haveI hpm : p.IsMaximal := (w.under (𝓞 K)).isMaximal
  have hwmem : w.asIdeal ∈ IsDedekindDomain.primesOverFinset p (𝓞 L) :=
    (IsDedekindDomain.mem_primesOverFinset_iff hp0 (𝓞 L)).2 ⟨w.isPrime, inferInstance⟩
  have humem : u.asIdeal ∈ IsDedekindDomain.primesOverFinset p (𝓞 L) :=
    (IsDedekindDomain.mem_primesOverFinset_iff hp0 (𝓞 L)).2 ⟨u.isPrime, inferInstance⟩
  have hneI : u.asIdeal ≠ w.asIdeal := fun h => hne (HeightOneSpectrum.ext h)
  have hsum := Ideal.sum_ramification_inertia (𝓞 L) K L (p := p) hp0
  rw [Algebra.IsQuadraticExtension.finrank_eq_two K L] at hsum
  have hterm : ∀ P ∈ IsDedekindDomain.primesOverFinset p (𝓞 L), 1 ≤ p.ramificationIdx' P * p.inertiaDeg' P := by
    intro P hP
    obtain ⟨hPp, hPl⟩ := (IsDedekindDomain.mem_primesOverFinset_iff hp0 (𝓞 L)).1 hP
    haveI := hPp; haveI := hPl
    have h1 : 0 < p.ramificationIdx' P := by
      rw [Ideal.ramificationIdx'_eq_ramificationIdx p P hp0]
      exact Ideal.ramificationIdx_pos (R := 𝓞 K) P
    have h2 : 0 < p.inertiaDeg' P := Ideal.inertiaDeg'_pos p P
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero h1.ne' h2.ne')
  have hpair : ({w.asIdeal, u.asIdeal} : Finset (Ideal (𝓞 L))) ⊆ IsDedekindDomain.primesOverFinset p (𝓞 L) := by
    intro P hP
    simp only [Finset.mem_insert, Finset.mem_singleton] at hP
    rcases hP with rfl | rfl
    · exact hwmem
    · exact humem
  have hle := Finset.sum_le_sum_of_subset (f := fun P => p.ramificationIdx' P * p.inertiaDeg' P) hpair
  rw [Finset.sum_pair hneI.symm, hsum] at hle
  have hu1 := hterm _ humem
  have hw1 : p.ramificationIdx' w.asIdeal * p.inertiaDeg' w.asIdeal = 1 := by
    have := hterm _ hwmem
    omega
  have he : p.ramificationIdx' w.asIdeal = 1 := Nat.eq_one_of_mul_eq_one_right hw1
  rw [Ideal.ramificationIdx'_eq_ramificationIdx p w.asIdeal hp0] at he
  exact (Algebra.isUnramifiedAt_iff_of_isDedekindDomain).2 he

end GlobalTheory.SplitUnram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MeasureEqOfMoments
section
open GlobalTheory.MomOne GlobalTheory.MomN PowerSeries
open scoped ComplexConjugate

namespace GlobalTheory.MomN

theorem measure_eq_of_moments : ∀ (q : ℕ) [Fact q.Prime] (κ : Type) [Fintype κ]
    (μ μ' : C(κ → ℤ_[q], ℂ_[q]) →L[ℂ_[q]] ℂ_[q]),
    (∀ (k : ℕ) (j : Fin k → κ) (f : C(κ → ℤ_[q], ℂ_[q])),
      (∀ a, f a = ∏ l, zc (a (j l))) → μ f = μ' f) → μ = μ' := by
  intro q _ κ _ μ μ' h
  let e := Fintype.equivFin κ
  let π : C(κ → ℤ_[q], Fin (Fintype.card κ) → ℤ_[q]) :=
    ⟨fun b i => b (e.symm i), by fun_prop⟩
  let π' : C(Fin (Fintype.card κ) → ℤ_[q], κ → ℤ_[q]) :=
    ⟨fun a i => a (e i), by fun_prop⟩
  let Φ : C(Fin (Fintype.card κ) → ℤ_[q], ℂ_[q]) →L[ℂ_[q]] C(κ → ℤ_[q], ℂ_[q]) :=
    { toFun := fun G => G.comp π
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      cont := ContinuousMap.continuous_precomp π }
  have hz : (μ - μ').comp Φ = 0 := by
    exact GlobalTheory.MonomialDense.eq_zero_of_monomials q _ _ fun m k g hg => by
      have := h m (fun l => e.symm (k l)) (Φ g) fun b => hg (π b)
      simp [this]
  ext F
  have hF : Φ (F.comp π') = F := by
    ext b
    change F (π' (π b)) = F b
    congr 1
    funext i
    simp [π, π']
  have := congrArg (fun ν => ν (F.comp π')) hz
  simp only [ContinuousLinearMap.comp_apply, hF, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.zero_apply] at this
  exact sub_eq_zero.mp this

end GlobalTheory.MomN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MoveStepOfFamily
section
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.ThetaMove

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV _root_.Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

theorem moveLaw_at (X : Fields) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S)
    (cst : LocCst X (rowSG Pr sel mu)) (u : Pr.Word)
    (D : D7) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)
    (hX : X.Ok) (hPr : Pr.Ok) (hCh : Ch.FromHecke W s.σ₀) (hsel : IsSel X sel) (hT : Pr.T u ∈ S) (hg : ∀ k, Pr.g k ∈ S)
    (hs : s.Ok) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hχ : TaylorLogMetric.IsChi D χ)
    (hcop : ∀ P ∈ Sall sel mu u, Nat.Coprime (Ideal.absNorm cc) (Ideal.absNorm P.asIdeal))
    (hEq : B.EqP χ) (hLat : B.LatAll) (hTh : ∀ a b, Even a → Even b → B.ThZeroMem a b)
    (i : ℕ) (hi : i < R.m) (b : ℕ) (hb : b = R.N (i + 1)) (lam' : X.Tau → DomWeight b)
    (N₁ N₂ : Submodule (𝓞 X.E) (Sp X.E (R.N i))) (N₁' N₂' : Submodule (𝓞 X.E) (Sp X.E b))
    (fr : Frs X.E (R.N i) (rowSG Pr sel mu)) (fr' : Frs X.E b (rowSG Pr sel mu)) (Ξ : HomE X.E (R.N i) b → X.K)
    (h₁ : IsSdLat N₁) (h₂ : IsSdLat N₂) (h₁' : IsSdLat N₁') (h₂' : IsSdLat N₂')
    (ag : AgreeOff (Pr.T u) N₁ N₂) (ag' : AgreeOff (Pr.T u) N₁' N₂')
    (b₁ : InBox (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N₁ N₁' Ξ)
    (b₂ : InBox (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N₂ N₂' Ξ)
    (j₁ : JetsIn (ambOf s B χ cD) (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) (W.lamTrue u i) (nuLast W u i) N₁ N₁')
    (j₂ : JetsIn (ambOf s B χ cD) (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) (W.lamTrue u i) (nuLast W u i) N₂ N₂') :
    kerOf (stepT W Ch sel mu cst (ambOf s B χ cD) u i lam') (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N₁ fr N₁' fr' Ξ =
      moveScal Ch mu u i N₁ N₂ N₁' N₂' •
        kerOf (stepT W Ch sel mu cst (ambOf s B χ cD) u i lam') (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N₂ fr N₂' fr' Ξ := by
  classical
  have ea : Even (R.N i) := even_N R i
  have eb : Even b := hb ▸ even_N R (i + 1)
  have hA := GlobalTheory.ThetaMove.SeamMoves.moves_ambOf X D s cc δ B χ cD (R.N i) b hX hs hcc hχ hEq hLat
    (hTh _ _ ea eb) ea eb
  have bad := GlobalTheory.ThetaMove.BadPrimes.bad_primes X Pr sel S mu u hX hPr hsel hT hg
  have hU : (ambOf s B χ cD).AAUnit (Sall sel mu u) := fun P hP =>
    GlobalTheory.PeriodIdealUnit.locP_AA_eq_one X D s cc δ B χ cD P (bad P hP).2.1 (bad P hP).2.2.1 (hcop P hP)
  set A := ambOf s B χ cD with hAdef
  set Sa := Sall sel mu u with hSa
  have hq : 0 < ∏ P : rowSG Pr sel mu, Formalism.L2.Col.qOf P.1 :=
    Finset.prod_pos fun P _ => Nat.pos_of_ne_zero fun h => P.1.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hTpos : 0 < Pr.T u := (hPr.T_prime u).pos
  have hcA : 0 < cAof sel mu cst := pow_pos hq _
  have hcB : 0 < cBof sel mu cst u := Nat.mul_pos hTpos (pow_pos hq _)
  have hoff : ∀ Q : HeightOneSpectrum (𝓞 X.E), Q ∉ Sa → conjPrime₂ Q ∉ Sa → ((Pr.T u : ℕ) : 𝓞 X.E) ∉ Q.asIdeal := by
    intro Q h h' hQ
    rw [← hPr.piT_norm u] at hQ
    rcases Q.isPrime.mem_or_mem hQ with h1 | h1
    · exact h (Finset.mem_union_left _ ((mem_divs (hPr.piT_ne_zero u) Q).2 h1))
    · exact h' (Finset.mem_union_left _ ((mem_divs (hPr.piT_ne_zero u) _).2 ((mem_conjP Q _).2 h1)))
  have hord : ∀ {n : ℕ} {M M' : Submodule (𝓞 X.E) (Sp X.E n)} {P : HeightOneSpectrum (𝓞 X.E)},
      localization₂ P.asIdeal M = localization₂ P.asIdeal M' → ordDet P M = ordDet P M' := fun h => by
    unfold ordDet frameAt
    rw [h]
  let ex : HeightOneSpectrum (𝓞 X.E) → ℤ := fun P =>
    ((b / 2 : ℕ) : ℤ) * idxExp P N₁ N₂ - ((R.N i / 2 : ℕ) : ℤ) * idxExp P N₁' N₂'
  have hTR : (0 : ℝ) < (Pr.T u : ℝ) := by exact_mod_cast hTpos
  have hρ2 : (∏ P ∈ Pr.vT u, (Pr.T u : ℝ) ^ ex P) ^ 2 =
      ∏ P ∈ Sa, ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (volExp P N₂ N₂' - volExp P N₁ N₁') := by
    rw [← Finset.prod_pow, ← Finset.prod_subset (s₁ := Pr.vT u) (s₂ := Sa) Finset.subset_union_left]
    · refine Finset.prod_congr rfl fun P hP => ?_
      rw [hPr.vT_norm u P hP, ← zpow_natCast, ← zpow_mul]
      congr 1
      obtain ⟨a', ha'⟩ := ea
      obtain ⟨b', hb'⟩ := eb
      have e1 : R.N i / 2 = a' := by omega
      have e2 : b / 2 = b' := by omega
      have e3 : (R.N i : ℤ) = 2 * a' := by omega
      have e4 : (b : ℤ) = 2 * b' := by omega
      simp only [ex, volExp, idxExp, e1, e2, e3, e4]
      push_cast
      ring
    · intro P hP hP'
      have h1 : ((Pr.T u : ℕ) : 𝓞 X.E) ∉ P.asIdeal := fun h => hP' ((bad P hP).2.2.2.1 h)
      rw [volExp, volExp, hord (ag P h1), hord (ag' P h1), sub_self, zpow_zero]
  have box : ∀ {N : Submodule (𝓞 X.E) (Sp X.E (R.N i))} {N' : Submodule (𝓞 X.E) (Sp X.E b)},
      InBox Sa (cAof sel mu cst) (cBof sel mu cst u) N N' Ξ →
      InBox Sa (cAof sel mu cst) (cBof sel mu cst u) N N' fun x => A.σ₀ (Ξ x) := fun h =>
    ⟨fun x hx => h.1 x fun h0 => hx (by simp [h0]), fun x y hy => by simp only [h.2 x y hy]⟩
  have hcore := core hA (fun P hP => (bad P hP).1) hU h₁ h₂ h₁' h₂' (fun Q h h' => ag Q (hoff Q h h'))
    (fun Q h h' => ag' Q (hoff Q h h')) hcA hcB (box b₁) (box b₂) (Finset.prod_pos fun P _ => zpow_pos hTR _) hρ2
  have full_of_sd : ∀ {n : ℕ} {L : Submodule (𝓞 X.E) (Sp X.E n)}, IsSdLat L → Submodule.IsFullLattice X.E L := by
    intro n L hL
    let := hL.1
    refine { span_eq_top := ?_ }
    let W := Submodule.span X.E (L : Set (Sp X.E n))
    change W = ⊤
    by_contra hW
    let e : Sp X.E n ≃ₗ⋆[X.E] Sp X.E n := starLinearEquiv X.E
    let g : Sp X.E n →ₗ[X.E] Module.Dual X.E W :=
      (LinearMap.domRestrict' W).comp ((hStd X.E n).comp e.toLinearMap)
    have hdim : Module.finrank X.E (Module.Dual X.E W) < Module.finrank X.E (Sp X.E n) := by
      rw [Subspace.dual_finrank_eq]
      exact Submodule.finrank_lt hW
    obtain ⟨x, hx, hx₀⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
    have hsmul (a : X.E) : a • e x ∈ L := by
      rw [← hL.2, dualBasic_mem_dual]
      intro y hy
      apply hStd_mem_one_symm
      have hxy : hStd X.E n (e x) y = 0 :=
        congrArg (fun f : Module.Dual X.E W => f ⟨y, Submodule.subset_span hy⟩) (LinearMap.mem_ker.mp hx)
      simp [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hxy]
    let i : X.E →ₗ[𝓞 X.E] L :=
      ((LinearMap.toSpanSingleton X.E _ (e x)).restrictScalars (𝓞 X.E)).codRestrict L hsmul
    let : Module.Finite (𝓞 X.E) L := Module.Finite.iff_fg.mpr hL.1.fg
    let : Module.Finite (𝓞 X.E) X.E := Module.Finite.of_injective i fun a b hab =>
      smul_left_injective X.E (fun hz => hx₀ (e.map_eq_zero_iff.mp hz)) (congrArg Subtype.val hab)
    exact RingOfIntegers.not_isField X.E
      (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 X.E) X.E) (Field.toIsField X.E))
  have f₁ := GlobalTheory.finite_divLat_quot_mulLat_homAt X.E _ _ Sa N₁ N₁' _ _ (full_of_sd h₁) h₁'.1 hcA hcB
  have f₂ := GlobalTheory.finite_divLat_quot_mulLat_homAt X.E _ _ Sa N₂ N₂' _ _ (full_of_sd h₂) h₂'.1 hcA hcB
  have := @Fintype.ofFinite _ f₁
  have := @Fintype.ofFinite _ f₂
  have hj := GlobalTheory.jetOp_identity_of_entire X (R.N i) b A.σ₀ A.cD (W.lamTrue u i) lam' (nuLast W u i) _ _ _ _ _ _ (A.chiF _ _ N₁ N₁')⁻¹ (A.chiF _ _ N₂ N₂')⁻¹
    (∏ P ∈ Pr.vT u, (Pr.T u : X.K) ^ ex P)
    (fun q => analytic_thInd (S := Sa) hA h₁ h₁' (cBof sel mu cst u)
      (Function.surjInv (Submodule.Quotient.mk_surjective _) q : ↥(divLat (cAof sel mu cst) (homAt Sa N₁ N₁'))))
    (fun q => analytic_thInd (S := Sa) hA h₂ h₂' (cBof sel mu cst u)
      (Function.surjInv (Submodule.Quotient.mk_surjective _) q : ↥(divLat (cAof sel mu cst) (homAt Sa N₂ N₂'))))
    (fun q m hm => j₁ _ (Subtype.prop _) m hm) (fun q m hm => j₂ _ (Subtype.prop _) m hm)
    (fun z => by
      have h1 := hcore z
      unfold latSum at h1
      rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype] at h1
      refine h1.trans ?_
      congr 1
      simp)
  have hmU := mUof_conj W Ch sel mu u s.σ₀ hX hPr hCh hsel hT hg i hi
  have m₁ := GlobalTheory.MuOffMove.muOff_move X Pr sel S mu u _ _ N₁ N₂ hX hPr hsel hT hg hmU h₁ h₂ ag
  have m₂ := GlobalTheory.MuOffMove.muOff_move X Pr sel S mu u _ _ N₁' N₂' hX hPr hsel hT hg hmU h₁' h₂' ag'
  unfold stepT
  rw [kerOf_eq, kerOf_eq]
  refine (congrArg _ hj).trans ?_
  rw [smul_smul, smul_smul]
  congr 1
  have hsc : moveScal Ch mu u i N₁ N₂ N₁' N₂' =
      (∏ P ∈ Pr.vT u, ((mUof Ch mu i P ^ (-idxExp P N₁ N₂) : X.Kˣ) : X.K)) *
        (∏ P ∈ Pr.vT u, ((mUof Ch mu i P ^ (-idxExp P N₁' N₂') : X.Kˣ) : X.K))⁻¹ * ∏ P ∈ Pr.vT u, (Pr.T u : X.K) ^ ex P := by
    rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun P _ => ?_
    rw [locScal, ← Units.val_inv_eq_inv_val, ← Units.val_mul, ← zpow_neg, ← zpow_add]
    congr 3
    ring
  rw [hsc, muInvDet, muInvDet, muInvDet, muInvDet, m₁, m₂]
  simp only [mul_inv]
  ring


open GlobalTheory.KerT in
theorem moveStep_of_family : ∀ (Z : Dat) (H : D7) (s : Seam H Z.X) (cc : Ideal (𝓞 H.host.K)) (δ : ℂ) (B : Base H cc δ)
    (χ : TaylorLogMetric.IdE H → ℂ) (cD : H.what₂.Tau → ℂ) (sel : HeightOneSpectrum (𝓞 Z.X.F) → HeightOneSpectrum (𝓞 Z.X.E)) (S : Set ℕ)
    (mu : Tup Z.X.F Z.X.E Z.X.K S) (cst : LocCst Z.X (rowSG Z.Pr sel mu)) (u : Z.Pr.Word) (i : ℕ), i < Z.R.m →
    Hyp Z s cc δ χ cD sel S mu cst u → B.EqP χ → B.LatAll → (∀ a b, Even a → Even b → B.ThZeroMem a b) →
    GlobalTheory.KerT.JetsAll Z.W sel mu cst (ambOf s B χ cD) u i (i + 1) →
    MoveStep Z.W Z.Ch sel mu cst (ambOf s B χ cD) u i (i + 1) := by
  intro Z H s cc δ B χ cD sel S mu cst u i hi h hEq hLat hTh hJ N₁ N₂ N₁' N₂' fr fr' Ξ h₁ h₂ h₁' h₂' ag ag' b₁ b₂
  obtain ⟨hs, hσ, hcc, -, hχ, -⟩ := h.ana
  exact moveLaw_at Z.X Z.Pr Z.R Z.W Z.Ch sel S mu cst u H s cc δ B χ cD h.ok.fields h.ok.primes (hσ ▸ h.ok.hecke) h.isSel h.T_mem
    h.g_mem hs hcc hχ h.cop hEq hLat hTh i hi _ rfl _ N₁ N₂ N₁' N₂' fr fr' Ξ h₁ h₂ h₁' h₂' ag ag' b₁ b₂ (hJ _ _ h₁ h₁') (hJ _ _ h₂ h₂')

end GlobalTheory.ThetaMove
end
end

