module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ToFirst
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TranslDiffEq
public import Development.WeilBound.CoreStatements.HodgeTatePoints.IsPullbackWhisker
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0045
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0049
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0165
public import Development.WeilBound.CoreStatements.HodgeTatePoints.QamCore
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0180
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0088
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0168
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.CocpMain
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.HtPt.Cocp

theorem cocycle_p : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (hp : 1 ≤ p) (x : Sp k ⟶ X0) (d : ℕ) (g : GermAt t x d) (w : Fin d → k), alpha g.B p (fun i => w i ^ p) = 0 → ∃ c : LB.Gen (Out.translDiff t.G t.PP.L (homAt x (toFirst k p hp) ≫ (homAt x (jetSubstP p fun q : Fin 1 × Fin d => MvPolynomial.C (w q.2) * MvPolynomial.X ()) ≫ g.x p : overAt x (Jet k Unit p) ⟶ t.G))), c.IsGen := by
  intro E _ _ _ H _ hstar X0 t k _ _ p _ _ hp x d g w hα
  obtain ⟨hy0, hy1, -⟩ := PositivityTheory.HtPt.Ce.pt_of_vec E H hstar X0 t k p hp x d g w
  have hwv : (hw g.B p).mulVec (fun i => w i ^ p) = 0 := by
    have := congrArg Prod.fst hα
    rwa [alpha_apply] at this
  have hyp := hy1 hwv
  obtain ⟨gs, hax, hpow, -⟩ := GlobalTheory.T.pow_one_series_p_formula k p d (𝓞 E) g.B
  have hkill := GlobalTheory.T.alpha_kernel_derivative_vanishes k p d (𝓞 E) g.B (fun i => w i ^ p) gs hα hpow
  have hf : ∀ q, MvPowerSeries.pderiv (R := k) q (dSer gs fun i => w i ^ p) = 0 := by
    rintro ⟨i, j⟩
    obtain rfl : i = 0 := Subsingleton.elim _ _
    exact hkill j
  obtain ⟨hI, hN, hCh, hT⟩ := GlobalTheory.T.formal_germ_jet_lift E H hstar X0 t k p x d g (fun m => xkZ t.G x (g.x m))
    (fun m => xkZ_fst t.G x _) (fun m => xkZ_snd t.G x _)
  obtain ⟨C, hC, hnorm, hB⟩ := GlobalTheory.CompanionTheory.Ar.Coc.Pf.pfold E H hstar X0 t k p x d g w gs hax hpow _ rfl hy0 hyp
  have hL := t.PP.isLB
  have hsub : Subsingleton (Sp k) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  obtain ⟨s⟩ : Nonempty (Sp k) := inferInstanceAs (Nonempty (PrimeSpectrum k))
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, ⊤ ≤ (1 : overAt x k ⟶ t.G).left ⁻¹ᵁ t.PP.L.U j₀ := by
    have hc := hL.cover
    have : (1 : overAt x k ⟶ t.G).left s ∈ (⊤ : t.G.left.Opens) := trivial
    rw [← hc] at this
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    refine ⟨j, fun s' _ => ?_⟩
    have e : s' = s := Subsingleton.elim (α := Sp k) _ _
    rw [e]
    exact hj
  have hU : ∀ m, ⊤ ≤ xkZ t.G x (g.x m) ⁻¹ᵁ (pullback.fst t.G.hom x ⁻¹ᵁ t.PP.L.U j₀) := by
    intro m q _
    have e : (homAt x (jetAug : Jet k (Fin 1 × Fin d) m →ₐ[k] k) ≫ g.x m).left = (1 : overAt x k ⟶ t.G).left :=
      congrArg (fun q => q.left) (g.chart.zero m)
    have e₁ : pullback.fst t.G.hom x (xkZ t.G x (g.x m) q) = (g.x m).left q := by
      rw [← Scheme.Hom.comp_apply, xkZ_fst]
    have e₂ : (g.x m).left q = (1 : overAt x k ⟶ t.G).left s := by
      rw [← jet_pt m q s, ← e]
      rfl
    change pullback.fst t.G.hom x (xkZ t.G x (g.x m) q) ∈ t.PP.L.U j₀
    rw [e₁, e₂]
    exact hj₀ trivial
  haveI : Nonempty (pullback.fst t.G.hom x ⁻¹ᵁ t.PP.L.U j₀) :=
    ⟨⟨_, hU 0 (show (spMap ((jetAug : Jet k (Fin 1 × Fin d) 0 →ₐ[k] k) : Jet k (Fin 1 × Fin d) 0 →+* k) s) ∈ ⊤ from trivial)⟩⟩
  have main := PositivityTheory.HtPt.Qam.core_firstOrder X0 t.G k x p hp hN t.PP.L hL _ _ (prZ_fst t.G x p).symm (secZ_pa t.G x _ hy0) C hC hnorm j₀
    (fun c h hc => by
      obtain ⟨F, hF1, -, hF3⟩ := hT _ hU (c (Fin.last p))
      refine hF3 (GlobalTheory.T.pderiv_zero_of_jet_pth_power_diff k p d F _ hf fun m => ?_)
      obtain ⟨v, hv⟩ := hB j₀ hj₀ m
      refine ⟨v, ?_⟩
      have hr : ⊤ ≤ rQ t.G x p (g.x m) ⁻¹ᵁ (prZ t.G x p ⁻¹ᵁ (pullback.fst t.G.hom x ⁻¹ᵁ t.PP.L.U j₀)) := by
        intro q _
        have e : prZ t.G x p (rQ t.G x p (g.x m) q) = xkZ t.G x (g.x m)
            (spMap ((inR (k := k) (Jet k (Fin 1 × Fin d) m) p : Jet k (Fin 1 × Fin d) m →ₐ[k] Jet (Jet k (Fin 1 × Fin d) m) Unit p) : Jet k (Fin 1 × Fin d) m →+* Jet (Jet k (Fin 1 × Fin d) m) Unit p) q) := by
          rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, rQ_prZ]
        change prZ t.G x p (rQ t.G x p (g.x m) q) ∈ (pullback.fst t.G.hom x ⁻¹ᵁ t.PP.L.U j₀)
        rw [e]
        exact hU m trivial
      have hr' : ⊤ ≤ rQ t.G x p (g.x m) ⁻¹ᵁ LB.wchart t.PP.L (K := Fin 2) ![_, _] (fun _ => j₀) :=
        hr.trans fun q hq => h hq
      have h2 := _root_.GlobalTheory.CompanionTheory.Ar.Coc.coef_pull X0 t.G k x p hp _ (g.x m) _ (hU m) c _ (v ^ p - psJet m (dSer gs fun i => w i ^ p)) hc hr (by
        rw [← hv hr']
        exact congrArg (fun q => q.hom (C.s fun _ => j₀).val) (Scheme.Hom.map_appLE (rQ t.G x p (g.x m)) hr (homOfLE h).op))
      exact toΓ_inj _ ((hF1 m).symm.trans h2))
  rw [trY_pa, trY_pb] at main
  exact main

theorem tanpf_inj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X0) (d : ℕ) (g : GermAt t x d), TanPF t x p → ConjInj g.B p :=
  PositivityTheory.HtPt.Ce.tanpf_inj_of cocycle_p

end PositivityTheory.HtPt.Cocp
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.HtatPol
section
noncomputable section

namespace PositivityTheory.HtPt.Htat

open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem finrank_int_eq {E : Type} [Field E] [NumberField E] (M : Type) [AddCommGroup M] [Module (𝓞 E) M]
    [Module.Finite (𝓞 E) M] :
    Module.finrank ℤ M = Module.finrank (𝓞 E) M * Module.finrank ℚ E := by
  set S := Algebra.algebraMapSubmonoid (𝓞 E) (nonZeroDivisors ℤ)
  have hS : S ≤ nonZeroDivisors (𝓞 E) := by
    rintro _ ⟨n, hn, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero (by
      simpa using (FaithfulSMul.algebraMap_injective ℤ (𝓞 E)).ne (nonZeroDivisors.ne_zero hn))
  let f := TensorProduct.mk (𝓞 E) E M 1
  haveI hloc : IsLocalizedModule S f :=
    (isLocalizedModule_iff_isBaseChange S E f).mpr (TensorProduct.isBaseChange (𝓞 E) M E)
  haveI : IsLocalizedModule (nonZeroDivisors ℤ) (f.restrictScalars ℤ) :=
    IsLocalizedModule.restrictScalars (nonZeroDivisors ℤ) f
  have h1 := IsLocalizedModule.finrank_eq (nonZeroDivisors ℤ) (f.restrictScalars ℤ) le_rfl
  have h2 := IsLocalizedModule.finrank_eq S f hS
  have h3 := IsLocalization.finrank_eq E S hS (N := TensorProduct (𝓞 E) E M)
  have h4 := IsFractionRing.finrank_right_eq ℤ ℚ (TensorProduct (𝓞 E) E M)
  have h5 := Module.finrank_mul_finrank ℚ E (TensorProduct (𝓞 E) E M)
  rw [← h1, ← h4, ← h5, h3, h2, mul_comm]

private theorem exists_span_sup_maximal_smul_eq_top {R : Type} [CommRing R] [IsDomain R] (P : Ideal R) [hP : P.IsMaximal]
    (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M] :
    ∃ m : Fin (Module.finrank R M) → M, Submodule.span R (Set.range m) ⊔ P • ⊤ = ⊤ := by
  classical
  let Rp := Localization.AtPrime P
  let f := TensorProduct.mk R Rp M 1
  haveI hloc : IsLocalizedModule P.primeCompl f :=
    (isLocalizedModule_iff_isBaseChange P.primeCompl Rp f).mpr (TensorProduct.isBaseChange R M Rp)
  have hle : P.primeCompl ≤ nonZeroDivisors R := fun s hs =>
    mem_nonZeroDivisors_of_ne_zero (fun h => hs (h ▸ P.zero_mem))
  have hrank : Module.finrank Rp (TensorProduct R Rp M) = Module.finrank R M :=
    (IsLocalization.finrank_eq Rp P.primeCompl hle).trans (IsLocalizedModule.finrank_eq P.primeCompl f hle)
  haveI : Module.Free Rp (TensorProduct R Rp M) := Module.free_of_flat_of_isLocalRing
  let b := Module.finBasisOfFinrankEq Rp (TensorProduct R Rp M) hrank
  choose ms hms using fun i => IsLocalizedModule.mk'_surjective P.primeCompl f (b i)
  refine ⟨fun i => (ms i).1, ?_⟩
  set N := Submodule.span R (Set.range fun i => (ms i).1)
  have htop : Submodule.localized' Rp P.primeCompl f N = ⊤ := by
    rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact (Submodule.mem_localized' Rp P.primeCompl f N _).mpr
      ⟨(ms i).1, Submodule.subset_span ⟨i, rfl⟩, (ms i).2, hms i⟩
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, hy, t, hyt⟩ := (Submodule.mem_localized' Rp P.primeCompl f N (f x)).mp (htop ▸ Submodule.mem_top)
  rw [IsLocalizedModule.mk'_eq_iff, Submonoid.smul_def, ← map_smul] at hyt
  obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := P.primeCompl) hyt
  have hmem : ((c : R) * t) • x ∈ N := by
    rw [mul_smul, ← Submonoid.smul_def c, ← hc, Submonoid.smul_def]
    exact N.smul_mem _ hy
  have hnot : (c : R) * t ∉ P := (P.primeCompl.mul_mem c.2 t.2)
  obtain ⟨r, i, hi, hri⟩ := hP.exists_inv hnot
  have : x = (r * ((c : R) * t)) • x + i • x := by rw [← add_smul, hri, one_smul]
  rw [this]
  exact Submodule.add_mem _ (Submodule.mem_sup_left (by rw [mul_smul]; exact N.smul_mem r hmem))
    (Submodule.mem_sup_right (Submodule.smul_mem_smul hi Submodule.mem_top))

private theorem exists_finrank_family_mod_smul {R : Type} [CommRing R] [IsDedekindDomain R]
    (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    (n : ℕ) (hn : Module.finrank R M = n) (a : R) (ha : a ≠ 0) :
    ∃ u : Fin n → M, ∀ x : M, ∃ (c : Fin n → R) (x' : M), x = ∑ i, c i • u i + a • x' := by
  classical
  subst hn
  set F := (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {a})).toFinset
  have hprime : ∀ P ∈ F, Prime P := fun P hP =>
    UniqueFactorizationMonoid.prime_of_normalized_factor P (Multiset.mem_toFinset.mp hP)
  have hm : ∀ P ∈ F, ∃ m : Fin (Module.finrank R M) → M,
      Submodule.span R (Set.range m) ⊔ P • (⊤ : Submodule R M) = ⊤ := by
    intro P hP
    haveI : P.IsMaximal := Ideal.IsPrime.isMaximal (Ideal.isPrime_of_prime (hprime P hP))
      (by rw [← Ideal.zero_eq_bot]; exact (hprime P hP).ne_zero)
    exact exists_span_sup_maximal_smul_eq_top P M
  choose! m hm using hm
  have he : ∀ Q ∈ F, ∃ e : R, ∀ P ∈ F, e - (if P = Q then 1 else 0) ∈ P := by
    intro Q _
    obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := F) id (fun _ => 1)
      (fun i hi => hprime i hi) (fun i _ j _ h => h) (fun P => if P.1 = Q then 1 else 0)
    exact ⟨y, fun P hP => by simpa using hy P hP⟩
  choose! e he using he
  let u : Fin (Module.finrank R M) → M := fun i => ∑ Q ∈ F, e Q • m Q i
  have hdiff : ∀ P ∈ F, ∀ i, u i - m P i ∈ P • (⊤ : Submodule R M) := by
    intro P hP i
    have : u i - m P i = ∑ Q ∈ F, (e Q - if P = Q then 1 else 0) • m Q i := by
      simp only [u, sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul,
        Finset.sum_ite_eq, hP, if_true]
    rw [this]
    exact Submodule.sum_mem _ fun Q hQ => Submodule.smul_mem_smul (he Q hQ P hP) Submodule.mem_top
  set N := Submodule.span R (Set.range u) ⊔ Ideal.span {a} • (⊤ : Submodule R M)
  have hcov : ∀ P ∈ F, N ⊔ P • (⊤ : Submodule R M) = ⊤ := by
    intro P hP
    refine eq_top_iff.mpr ((hm P hP).symm.le.trans (sup_le ?_ le_sup_right))
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have : m P i = u i - (u i - m P i) := by abel
    rw [this]
    exact Submodule.sub_mem _
      (Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)))
      (Submodule.mem_sup_right (hdiff P hP i))
  have key : ∀ I J : Ideal R, N ⊔ I • (⊤ : Submodule R M) = ⊤ → N ⊔ J • (⊤ : Submodule R M) = ⊤ →
      N ⊔ (I * J) • (⊤ : Submodule R M) = ⊤ := by
    intro I J hI hJ
    refine eq_top_iff.mpr (hI.symm.le.trans (sup_le le_sup_left ?_))
    rw [Submodule.mul_smul]
    calc I • (⊤ : Submodule R M) = I • (N ⊔ J • ⊤) := by rw [hJ]
      _ = I • N ⊔ I • J • ⊤ := Submodule.smul_sup _ _ _
      _ ≤ N ⊔ I • J • ⊤ := sup_le_sup_right (Submodule.smul_le_right) _
  have hfac : ∀ s : Multiset (Ideal R), (∀ P ∈ s, P ∈ F) → N ⊔ s.prod • (⊤ : Submodule R M) = ⊤ := by
    intro s
    induction s using Multiset.induction_on with
    | empty => intro _; simp
    | cons P s ih =>
      intro h
      rw [Multiset.prod_cons]
      exact key _ _ (hcov P (h P (Multiset.mem_cons_self _ _)))
        (ih fun Q hQ => h Q (Multiset.mem_cons_of_mem hQ))
  have hN : N = ⊤ := by
    have := hfac (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {a}))
      (fun P hP => Multiset.mem_toFinset.mpr hP)
    rwa [Ideal.prod_normalizedFactors_eq_self (by simpa using ha), sup_eq_left.mpr le_sup_right] at this
  refine ⟨u, fun x => ?_⟩
  have hx : x ∈ N := hN ▸ Submodule.mem_top
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hy
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hz
  obtain ⟨x', _, rfl⟩ := hz
  exact ⟨c, x', rfl⟩

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField _root_.GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor in
theorem pol_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (p : ℕ) [Fact p.Prime], ∃ u : Fin (D.p + D.q) → D.La, IsPolLattice (IsCMField.complexConj E).toRingEquiv p D.EF u := by
  intro E _ _ _ H D p _
  haveI := D.fin
  haveI := D.proj
  have hfinZ : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  haveI : Module.IsTorsionFree (𝓞 E) D.La := inferInstance
  haveI : Module.IsTorsionFree ℤ D.La := Module.IsTorsionFree.trans (𝓞 E)
  obtain ⟨u, hu⟩ := exists_finrank_family_mod_smul D.La (D.p + D.q) D.rank (p : 𝓞 E)
    (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  refine ⟨u, ⟨inferInstance, hfinZ, D.alt, D.unimod, ?_, ?_, ?_⟩⟩
  · intro a x y
    rw [D.adj]
    congr 2
    ext
    simp [H.bar_eq]
  · rw [finrank_int_eq (E := E), D.rank]
  · intro x
    obtain ⟨a, x', hx⟩ := hu x
    exact ⟨a, x', by rw [hx, Nat.cast_smul_eq_nsmul]⟩

end PositivityTheory.HtPt.Htat
end
end

