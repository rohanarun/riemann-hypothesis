module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidualChains.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0043
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.Bundle0009
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.ArithmeticPointDecomposition
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.QuadraticSplitting.QuadSplit
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0019
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0017
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.GaloisRepExistsTotallyRealGL2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AAcross

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ChainSeedRes
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws
section
variable {R R' : Type} [CommRing R] [CommRing R']
private theorem adj_map (j : R →+* R') (X : M4 R) : adj (X.map j) = (adj X).map j := by
  ext i i'
  simp only [adj_apply, Matrix.map_apply, map_zsmul]
private theorem conj_map (j : R →+* R') (n X : M4 R) :
    adj (n.map j) * X.map j * n.map j = (adj n * X * n).map j := by
  rw [Matrix.map_mul, Matrix.map_mul, adj_map]
private theorem isGSp_map (j : R →+* R') {ν : R} {X : M4 R} (hX : IsGSp ν X) : IsGSp (j ν) (X.map j) := by
  have h : (j ν) • (1 : M4 R') = (ν • (1 : M4 R)).map j := by
    ext i i'
    by_cases h : i = i' <;> simp [Matrix.one_apply, h]
  unfold IsGSp at hX ⊢
  rw [adj_map, ← Matrix.map_mul, h, hX]
private theorem isPair_map {O Γ : Type} [CommRing O] [Group Γ] (Φ : Fr O Γ) (a : O →+* R) (f : R →+* R')
    (P : PD Φ.ι Γ R) (h : Φ.IsPair a P) : Φ.IsPair (f.comp a) (P.map f) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have hr : ∀ g, (P.map f).r g = (P.r g).map f := fun _ => rfl
  have hn : ∀ v, (P.map f).n v = (P.n v).map f := fun _ => rfl
  refine ⟨fun g => isGSp_map f (h1 g), fun g hg => ?_, ?_, fun v => ⟨?_, fun i => ?_, fun i j hij => ?_⟩,
    fun v s hs i j hij => ?_, fun v s hs i => ?_⟩
  · rw [hr, h2 g hg, Matrix.map_one _ (map_zero f) (map_one f)]
  · rw [hr]; exact h3.map (map_zero f)
  · have := isGSp_map f (h4 v).1
    rwa [map_one] at this
  · rw [hn, Matrix.map_apply, (h4 v).2.1, map_one]
  · rw [hn, Matrix.map_apply, (h4 v).2.2 i j hij, map_zero]
  · rw [hr, hn, conj_map, Matrix.map_apply, h5 v s hs i j hij, map_zero]
  · have := h6 v s hs i
    unfold PD.ψ at this ⊢
    rw [hr, hn, conj_map, Matrix.map_apply, this, map_one]
end
theorem UpperTheory.V.Ws.Chain.isRes_map_red_and_inV_ent_map_red_of_map_residue :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D) (ι : PadicAlgCl l ≃+* ℂ) (𝔞 : Amb l) {c₁ : Coef l} (h : c.O ≤ c₁.O) (Q : PD T.ι (G T.F Ω) c₁.O),
      T.SeedPairAlt ι h Q → (T.fr ∅).IsRes (𝔞.red c) (Q.map (𝔞.red c₁)) ∧
        (Fr.InV (Φ := T.fr ∅) (Q.map (residue c₁.O)) → Fr.InV (Φ := T.fr ∅) (Q.map (𝔞.red c₁))) ∧
        ∀ w, Ent (Q.map (residue c₁.O)).r w → Ent (Q.map (𝔞.red c₁)).r w := by
  intro Ω _ _ _ l _ c D T ι 𝔞 c₁ h Q hQ
  have hj : Function.Injective (𝔞.j c₁) := (𝔞.j c₁).injective
  have hjr : ∀ x, 𝔞.red c₁ x = 𝔞.j c₁ (residue c₁.O x) := fun x => rfl
  have hQm : Q.map (𝔞.red c₁) = (Q.map (residue c₁.O)).map (𝔞.j c₁) := rfl
  have ha : 𝔞.red c = (𝔞.j c₁).comp ((residue c₁.O).comp (inc h)) := by
    ext x
    change residue _ (𝔞.a c x) = residue _ (𝔞.a c₁ (Subalgebra.inclusion h x))
    rw [𝔞.compat]
  have hres : (T.fr ∅).IsRes ((residue c₁.O).comp (inc h)) (Q.map (residue c₁.O)) := by
    refine ⟨isPair_map _ _ _ _ hQ.pair, hQ.res, fun i j N => ?_⟩
    have h1 := hQ.cont i j 1
    have h2 : IsLocallyConstant fun g => residue c₁.O (Q.r g i j) := by
      have := h1.comp (Ideal.Quotient.factor (show maximalIdeal c₁.O ^ 1 ≤ maximalIdeal c₁.O by rw [pow_one]))
      exact this
    exact h2.comp _
  refine ⟨?_, ?_, ?_⟩
  · rw [ha, hQm]
    exact (chainMap (T.fr ∅) _ (𝔞.j c₁) _).1.2 hres
  · rintro ⟨h1, h2⟩
    refine ⟨fun g i j hij hw => ?_, fun v => ⟨fun i j hij hw => ?_, fun h0 => (h2 v).2 ?_⟩⟩
    · exact (congrArg (𝔞.j c₁) (h1 g i j hij hw)).trans (map_zero _)
    · exact (congrArg (𝔞.j c₁) ((h2 v).1 i j hij hw)).trans (map_zero _)
    · exact hj (h0.trans (map_zero _).symm)
  · rintro w ⟨g, i, j, hw, hne⟩
    exact ⟨g, i, j, hw, fun h0 => hne (hj (h0.trans (map_zero _).symm))⟩
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.CharpolyConj
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.GalN.V
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws
section SlopeTestRemainingChoices
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
private theorem ps_wt_any {D : Raw Ω c} (h : D.Good) {A : ValuationSubring Ω} (hA : A.valuation (l : Ω) < 1) (i : Fin 4)
    {s : G ℚ Ω} (hs : s ∈ Ine (F := ℚ) A) (h1 : s ∈ D.ψ.ker) (h2 : s ∈ D.om.ker) :
    D.ps i s = chiO ℚ Ω l c.O s ^ D.wts4 i := by
  have hl : l.Prime := Fact.out
  obtain ⟨u, -, hu⟩ := (UpperTheory.V.Chr.placesQ Ω).2.2 l A _ hl hA (h.pl_over l hl)
  have e : ∀ γ : G ℚ Ω →* c.Oˣ, γ (u⁻¹ * s * u) = γ s := fun γ => by
    rw [map_mul, map_mul, map_inv, mul_right_comm, inv_mul_cancel, one_mul]
  have h3 := (facts D h).2.2.2.1 i (u⁻¹ * s * u) ⟨⟨hu s hs, (e _).trans h1⟩, (e _).trans h2⟩
  rwa [e, e] at h3
private theorem map_psi {ι Γ R R' : Type} [Group Γ] [CommRing R] [CommRing R'] (P : PD ι Γ R) (f : R →+* R') (v : ι) (i : Fin 4)
    (s : Γ) : (P.map f).ψ v i s = f (P.ψ v i s) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [PD.ψ, PD.map, Matrix.mul_apply, adj_apply, map_sum]
private theorem charpoly_conj {H K K' : Type} [Group H] [Field K] [Field K'] (f : K →+* K') {r r' : H →* M4 K}
    (h : IsConj4 r r') (g : H) : (mapRep f r g).charpoly = (mapRep f r' g).charpoly := by
  obtain ⟨u, hu⟩ := h
  show ((r g).map f).charpoly = ((r' g).map f).charpoly
  rw [Matrix.charpoly_map, Matrix.charpoly_map, hu, Matrix.coe_units_inv, Matrix.charpoly_units_conj]
end SlopeTestRemainingChoices
theorem UpperTheory.V.Ws.pureW_of_proModular_of_isZero :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (ι : PadicAlgCl l ≃+* ℂ) (𝔞 : Amb l) (e : 𝔞.K ≃+* PadicAlgCl l), 𝔞.IsZero e → ∀ r, _root_.UpperTheory.V.Ws.ProModAlt D ι 𝔞 r → PureW ι (mapRep ((e : 𝔞.K →+* PadicAlgCl l).comp 𝔞.toK) r) := by
  intro Ω _ _ _ l _ c D hD ι 𝔞 e he r hr
  obtain ⟨T, c', h, X, J, y, r₁, -, -, hPM, hy, -, hJ, hconj, -, hres, hin⟩ := hr
  let f : 𝔞.V →+* PadicAlgCl l := (e : 𝔞.K →+* PadicAlgCl l).comp 𝔞.toK
  let y' : X.A →ₐ[c'.O] PadicAlgCl l :=
    { f.comp y with
      commutes' := fun x => by
        have h1 : y (algebraMap c'.O X.A x) = 𝔞.a c' x := DFunLike.congr_fun hy x
        exact (congrArg f h1).trans (he.1 c' x) }
  have hy' : ∀ x, y' x = f (y x) := fun _ => rfl
  have hw : T.Wts (fun i => 2 * D.wts4 i) (X.P.map (y' : X.A →+* PadicAlgCl l)) := mkWts4 <| by
    have hc : Continuous (resQ T.F) := UpperTheory.V.Af.continuous_restrictScalarsHom ℚ T.F Ω
    refine ⟨(D.ψ.ker ⊓ D.om.ker).comap (resQ T.F),
      (hD.psi_open.inter (facts D hD).2.2.2.2.2.2.2.2.2.2.2.2.1).preimage hc, fun v i s hs => ?_⟩
    have h1 : resQ T.F s ∈ Ine (F := ℚ) (T.pl v) := hs.2
    have h2 := ps_wt_any hD (T.ovl v) i h1 hs.1.1 hs.1.2
    have h3 : f (y (X.P.ψ v i s)) = ((D.ps i (resQ T.F s) : c.O) : PadicAlgCl l) :=
      (congrArg f (hin v i s hs.2)).trans (he.1 c _)
    have h4 : (GlobalTheory.GalOfCusp.cycBar T.F Ω l s : PadicAlgCl l) =
      ((chiO ℚ Ω l c.O (resQ T.F s) : c.O) : PadicAlgCl l) := rfl
    refine (congrArg (· ^ 2) ((map_psi X.P _ v i s).trans h3)).trans ?_
    rw [h2]
    have h5 : (2 * (D.wts4 i : ℤ)) = ((D.wts4 i * 2 : ℕ) : ℤ) := by push_cast; ring
    simp only [h5, zpow_natCast, Units.val_pow_eq_pow_val, h4, SubmonoidClass.coe_pow, pow_mul]
  have hp := hPM.pur y' (fun b hb => by rw [hy', hJ b hb, map_zero]) hw (mapRep f r₁) (by
    ext g i j
    exact congrArg f (congrFun (congrFun (DFunLike.congr_fun hres g) i) j))
  obtain ⟨H, M, hH, hM, hp⟩ := _root_.UpperTheory.GalN.V.pureW' hp
  refine ⟨H, M, hH, hM, fun p h1 h2 A hA n σ hn hσ hF => ?_⟩
  have h3 : (mapRep f r σ).charpoly = (mapRep f r₁ σ).charpoly :=
    charpoly_conj (e : 𝔞.K →+* PadicAlgCl l) hconj σ
  rw [h3]
  exact hp p h1 h2 A hA n σ hn hσ hF
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ContradictionStarPromodular
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws
private theorem con_span {K Γ n : Type} [Field K] [Group Γ] [Fintype n] [DecidableEq n] [Nontrivial n]
    (σ : Γ → Matrix n n K) (hm : ∀ g h, σ (g * h) = σ g * σ h) (hs : Submodule.span K (Set.range σ) = ⊤)
    (P : Matrix n n K) (hP : IsUnit P)
    (ht : ∀ x g h, (P * σ (x * (g * h))).trace = (P * σ (x * (h * g))).trace) : False := by
  have h1 : ∀ g h, σ g * σ h = σ h * σ g := fun g h => by
    have h2 : ∀ M : Matrix n n K, (P * (M * (σ g * σ h))).trace = (P * (M * (σ h * σ g))).trace := fun M => by
      have hM : M ∈ Submodule.span K (Set.range σ) := hs ▸ Submodule.mem_top
      induction hM using Submodule.span_induction with
      | mem M hM => obtain ⟨x, rfl⟩ := hM; simpa only [hm] using ht x g h
      | zero => simp
      | add a b _ _ ha hb => simp only [add_mul, mul_add, Matrix.trace_add, ha, hb]
      | smul c a _ ha => simp only [smul_mul_assoc, mul_smul_comm, Matrix.trace_smul, ha]
    obtain ⟨u, rfl⟩ := hP
    ext i j
    have := h2 (((u⁻¹ : (Matrix n n K)ˣ) : Matrix n n K) * Matrix.single j i (1 : K))
    simpa only [mul_assoc, Units.mul_inv_cancel_left, Matrix.trace_single_mul, one_smul, smul_eq_mul, one_mul] using this
  have h3 : ∀ M N : Matrix n n K, M * N = N * M := fun M N => by
    have hM : M ∈ Submodule.span K (Set.range σ) := hs ▸ Submodule.mem_top
    have hN : N ∈ Submodule.span K (Set.range σ) := hs ▸ Submodule.mem_top
    induction hM, hN using Submodule.span_induction₂ with
    | mem_mem a b ha hb => obtain ⟨x, rfl⟩ := ha; obtain ⟨y, rfl⟩ := hb; exact h1 x y
    | zero_left => simp
    | zero_right => simp
    | add_left a b c _ _ _ h h' => simp only [add_mul, mul_add, h, h']
    | add_right a b c _ _ _ h h' => simp only [add_mul, mul_add, h, h']
    | smul_left r a b _ _ h => simp only [smul_mul_assoc, mul_smul_comm, h]
    | smul_right r a b _ _ h => simp only [smul_mul_assoc, mul_smul_comm, h]
  obtain ⟨i, j, hij⟩ := exists_pair_ne n
  have := congrFun (congrFun (h3 (Matrix.single i j 1) (Matrix.single j j 1)) i) j
  simp [hij, hij.symm] at this
private def con_e : Fin 2 ⊕ Fin 2 ≃ Fin 4 where
  toFun := Sum.elim ixA ixB
  invFun := ![Sum.inl 0, Sum.inr 0, Sum.inl 1, Sum.inr 1]
  left_inv := by decide
  right_inv := by decide
private theorem con_block {K Γ : Type} [Field K] [Group Γ] (r : Γ →* M4 K)
    (ht : ∀ x g h, (r (x * (g * h))).trace = (r (x * (h * g))).trace) (g0 : Γ) (hg : Squarefree (r g0).charpoly) :
    ¬ BlockExt r := by
  rintro ⟨h0, hs, -⟩
  have z : ∀ g (i j : Fin 2), r g (ixA i) (ixB j) = 0 := fun g i j => h0 g _ _ (by revert i j; decide)
  obtain ⟨A, hA⟩ : ∃ A : Γ → Matrix (Fin 2) (Fin 2) K, A = fun g => (r g).submatrix ixA ixA := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Γ → Matrix (Fin 2) (Fin 2) K, B = fun g => (r g).submatrix ixB ixB := ⟨_, rfl⟩
  rw [← hB] at hs
  have fb : ∀ g, (r g).submatrix con_e con_e = Matrix.fromBlocks (A g) 0 ((r g).submatrix ixB ixA) (B g) := fun g => by
    subst hA hB
    ext (i | i) (j | j)
    · rfl
    · exact z g i j
    · rfl
    · rfl
  have mAB : ∀ g h, A (g * h) = A g * A h ∧ B (g * h) = B g * B h := fun g h => by
    have h1 := fb (g * h)
    rw [map_mul, ← Matrix.submatrix_mul_equiv _ _ _ con_e, fb, fb, Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj] at h1
    obtain ⟨h2, -, -, h3⟩ := h1
    rw [Matrix.zero_mul, add_zero] at h2
    rw [Matrix.mul_zero, zero_add] at h3
    exact ⟨h2.symm, h3.symm⟩
  have mA := fun g h => (mAB g h).1
  have mB := fun g h => (mAB g h).2
  have tr : ∀ g, (r g).trace = (A g).trace + (B g).trace := fun g => by
    subst hA hB
    rw [Matrix.trace, ← Equiv.sum_comp con_e, Fintype.sum_sum_type]
    rfl
  have cp : (r g0).charpoly = (A g0).charpoly * (B g0).charpoly := by
    rw [← Matrix.charpoly_fromBlocks_zero₁₂, ← fb, ← Matrix.charpoly_reindex con_e.symm]
    rfl
  have ev : ∀ M : Matrix (Fin 2) (Fin 2) K, aeval M (A g0).charpoly = M * M - (A g0).trace • M + (A g0).det • 1 := fun M => by
    rw [Matrix.charpoly_fin_two]
    simp [Algebra.algebraMap_eq_smul_one, sq]
  have hU : IsUnit (aeval (B g0) (A g0).charpoly) := by
    rw [cp] at hg
    obtain ⟨u, v, huv⟩ := (IsRelPrime.of_squarefree_mul hg).isCoprime
    have := congrArg (aeval (B g0)) huv
    rw [map_add (f := _), map_mul, map_mul, Matrix.aeval_self_charpoly, mul_zero, add_zero, map_one] at this
    exact IsUnit.of_mul_eq_one_right _ this
  have key : ∀ y, (aeval (B g0) (A g0).charpoly * B y).trace =
      (r (g0 * g0 * y)).trace - (A g0).trace * (r (g0 * y)).trace + (A g0).det * (r y).trace := fun y => by
    have h1 : (aeval (A g0) (A g0).charpoly * A y).trace = 0 := by rw [Matrix.aeval_self_charpoly]; simp
    rw [ev] at h1 ⊢
    simp only [tr, mA, mB, add_mul, sub_mul, smul_mul_assoc, one_mul, Matrix.trace_add, Matrix.trace_sub,
      Matrix.trace_smul, smul_eq_mul] at h1 ⊢
    linear_combination -h1
  refine con_span B mB hs _ hU fun x g h => ?_
  rw [key, key, ht x, ← mul_assoc g0 x, ← mul_assoc g0 x, ht (g0 * x), ← mul_assoc _ x, ← mul_assoc _ x, ht (g0 * g0 * x)]
private theorem con_trace {K : Type} [Field K] [IsAlgClosed K] {l : ℕ} [Fact l.Prime] [CharP K l] (V : ValuationSubring K)
    (M : M4 V) (d : Fin 4 → V) (m N : ℕ) (hm : 0 < m) (hN : 0 < N) (hd : ∀ i, d i ^ m = 1)
    (hr : ∀ i, M i i - d i ∈ maximalIdeal V)
    (hc : ((M.map V.subtype) ^ N).charpoly = ∏ i, (X - C ((d i : K) ^ N))) : M.trace = ∑ i, d i := by
  haveI : CharP V l := RingHom.charP V.subtype Subtype.val_injective l
  letI : Algebra (ZMod l) V := ZMod.algebra V l
  letI : Algebra (ZMod l) K := ZMod.algebra K l
  let φ : V →ₐ[ZMod l] K := { V.subtype with commutes' := fun x => RingHom.congr_fun (RingHom.ext_zmod (V.subtype.comp (algebraMap _ _)) (algebraMap _ _)) x }
  have hdi : ∀ i, IsIntegral (ZMod l) (d i : K) := fun i => IsIntegral.of_pow hm (by
    have : (d i : K) ^ m = 1 := by exact_mod_cast congrArg Subtype.val (hd i)
    rw [this]; exact isIntegral_one)
  have h1 : IsIntegral (ZMod l) (M.map V.subtype).trace := by
    rw [Matrix.trace_eq_sum_roots_charpoly]
    refine IsIntegral.multiset_sum fun x hx => IsIntegral.of_pow hN ?_
    have h2 : x ∈ spectrum K (M.map V.subtype) :=
      Matrix.mem_spectrum_iff_isRoot_charpoly.2 (isRoot_of_mem_roots hx)
    have h3 := Matrix.mem_spectrum_iff_isRoot_charpoly.1 (spectrum.pow_mem_pow _ N h2)
    rw [hc, IsRoot.def, eval_prod, Finset.prod_eq_zero_iff] at h3
    obtain ⟨i, -, hi⟩ := h3
    rw [eval_sub, eval_X, eval_C, sub_eq_zero] at hi
    rw [hi]; exact (hdi i).pow N
  have h4 : IsIntegral (ZMod l) (M.trace - ∑ i, d i) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← isIntegral_algHom_iff φ Subtype.val_injective, map_sub, map_sum]
    refine IsIntegral.sub ?_ (IsIntegral.sum _ fun i _ => hdi i)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.trace, map_sum]
    exact h1
  have h5 : M.trace - ∑ i, d i ∈ maximalIdeal V := by
    rw [Matrix.trace, ← Finset.sum_sub_distrib]
    exact Ideal.sum_mem _ fun i _ => hr i
  by_contra hne
  exact h5 (h4.isUnit (sub_ne_zero.2 hne))
private theorem con_kill {l : ℕ} [Fact l.Prime] (𝔞 : Amb l) [CharP 𝔞.K l] (c : Coef l) (x y : c.O)
    (h : residue c.O x = residue c.O y) : 𝔞.a c x = 𝔞.a c y := by
  haveI : CharP 𝔞.V l := RingHom.charP 𝔞.V.subtype Subtype.val_injective l
  have h1 : RingHom.ker (𝔞.a c) ≠ ⊥ := fun h0 => by
    have h2 : (l : c.O) ∈ RingHom.ker (𝔞.a c) := by rw [RingHom.mem_ker, map_natCast, CharP.cast_eq_zero]
    rw [h0, Ideal.mem_bot] at h2
    exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast h2)
  have h3 : RingHom.ker (𝔞.a c) = maximalIdeal c.O := eq_maximalIdeal ((RingHom.ker_isPrime _).isMaximal h1)
  rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, h3]
  exact Ideal.Quotient.eq.1 h
private theorem con_const {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    {D : Raw Ω c} {ι : PadicAlgCl l ≃+* ℂ} {𝔞 : Amb l} [CharP 𝔞.K l] {r : G ℚ Ω →* M4 𝔞.V} (hp : _root_.UpperTheory.V.Ws.ProModAlt D ι 𝔞 r) :
    ∃ T : Tower D, T.Ok ∧ ∀ g : G T.F Ω, (mapRep 𝔞.toK r (resQ T.F g)).charpoly =
      ∏ i, (X - C (𝔞.toK (𝔞.a c (chi D T.pr i (resQ T.F g))))) := by
  obtain ⟨T, c', h, Y, J, y, r₁, ⟨hok, -⟩, -, hpm, hy, -, hJ, ⟨u, hu⟩, -, hr, hψ⟩ := hp
  refine ⟨T, hok, fun g => ?_⟩
  obtain ⟨n, hn⟩ := hpm.fin
  have hy' : ∀ x, (y.comp (algebraMap Y.B Y.A)) (algebraMap c'.O Y.B x) = 𝔞.a c' x := fun x => by
    rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply, ← hy, RingHom.comp_apply]
  have h1 : maximalIdeal Y.B ^ n ≤ RingHom.ker (y.comp (algebraMap Y.B Y.A)) := by
    refine hn.trans (sup_le (sup_le (fun b hb => hJ b hb) ?_) ?_)
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      rw [Ideal.mem_comap, RingHom.mem_ker, hy', ← map_zero (𝔞.a c')]
      exact con_kill 𝔞 c' _ _ (by rw [map_zero, residue_eq_zero_iff]; exact hx)
    · rw [Ideal.span_le]
      rintro _ ⟨v, i, s, hs, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one, RingHom.comp_apply, Y.ψ_map v i s (Ine_le_Dec _ hs),
        hψ v i s hs, sub_eq_zero, ← map_one (𝔞.a c)]
      refine con_kill 𝔞 c _ _ ?_
      have h2 := congrFun (congrFun (hok.ineL _ (T.ovl v) s hs) i) i
      rw [Matrix.one_apply_eq] at h2
      rw [map_one, ← h2]
      simp [Raw.rbar, Raw.r0, diagRep]
  have h2 : maximalIdeal Y.B ≤ RingHom.ker (y.comp (algebraMap Y.B Y.A)) :=
    (RingHom.ker_isPrime _).le_of_pow_le h1
  have h3 : RingHom.ker (res c'.O Y.B : Y.B →+* ResidueField c'.O) ≤ RingHom.ker (y.comp (algebraMap Y.B Y.A)) :=
    fun x hx => h2 ((res_eq_zero_iff c'.O Y.B x).1 hx)
  have hsurj : Function.Surjective (res c'.O Y.B : Y.B →+* ResidueField c'.O) := fun z => by
    obtain ⟨x, rfl⟩ := residue_surjective z
    exact ⟨algebraMap _ _ x, (res c'.O Y.B).commutes x⟩
  let j : ResidueField c'.O →+* 𝔞.V := RingHom.liftOfSurjective _ hsurj ⟨_, h3⟩
  have hj : j.comp (res c'.O Y.B : Y.B →+* ResidueField c'.O) = y.comp (algebraMap Y.B Y.A) :=
    RingHom.liftOfRightInverse_comp _ _ _ _
  have hj' : ∀ x, j (residue c'.O x) = 𝔞.a c' x := fun x => by
    rw [← hy', ← hj, RingHom.comp_apply]
    exact congrArg j ((res c'.O Y.B).commutes x).symm
  have h4 : (r₁ (resQ T.F g)).charpoly = ∏ i, (X - C (𝔞.a c (chi D T.pr i (resQ T.F g)))) := by
    have h5 : r₁ (resQ T.F g) = (Y.P.r g).map y := DFunLike.congr_fun hr g
    rw [h5, Matrix.charpoly_map, ← Y.cp_map, Polynomial.map_map, ← hj, ← Polynomial.map_map, Y.cp_red, Polynomial.map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Polynomial.map_sub, map_X, map_C, hj']
    exact congrArg (fun t => X - C t) (𝔞.compat c c' h _)
  have h6 : mapRep 𝔞.toK r₁ (resQ T.F g) = (r₁ (resQ T.F g)).map 𝔞.toK := rfl
  have h7 := congrArg Matrix.charpoly (hu (resQ T.F g))
  rw [Matrix.coe_units_inv, Matrix.charpoly_units_conj, h6, Matrix.charpoly_map, h4, Polynomial.map_prod] at h7
  rw [← h7]
  simp only [Polynomial.map_sub, map_X, map_C]
theorem UpperTheory.V.Ws.contradiction_star_promodular :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (ι : PadicAlgCl l ≃+* ℂ) (𝔞 : Amb l), CharP 𝔞.K l → ∀ r u, KPair D 𝔞 r u → _root_.UpperTheory.V.Ws.ProModAlt D ι 𝔞 r → ¬ Star (mapRep 𝔞.toK r) := by
  intro Ω _ _ _ l _ c D _ ι 𝔞 hch r u hk hp
  obtain ⟨T, hok, hc⟩ := con_const hp
  have hlab : Function.Bijective (lab T.pr) := by cases T.pr <;> decide
  haveI : Finite (ResidueField c.O) := (UpperTheory.V.abelian₂.dvr_finite l c.O).2.1
  haveI : IsGalois ℚ Ω := {}
  have htr : ∀ g, (r g).trace = ∑ i, 𝔞.a c (D.ps i g) := fun g => by
    have hi : T.F.fixingSubgroup.index ≠ 0 := by
      rw [← IntermediateField.finrank_eq_fixingSubgroup_index]
      exact Module.finrank_pos.ne'
    obtain ⟨N, hN, -, hg⟩ := Subgroup.exists_pow_mem_of_index_ne_zero hi g
    obtain ⟨g', hg'⟩ : ∃ g' : G T.F Ω, resQ T.F g' = g ^ N := ⟨T.F.fixingSubgroupEquiv ⟨_, hg⟩, rfl⟩
    refine con_trace (l := l) 𝔞.V (r g) _ (Nat.card (ResidueField c.O)ˣ) N Nat.card_pos hN (fun i => ?_) (fun i => ?_) ?_
    · rw [← map_pow, ← map_one (𝔞.a c)]
      refine con_kill 𝔞 c _ _ ?_
      have := congrArg Units.val (pow_card_eq_one' (x := Units.map (residue c.O : c.O →* ResidueField c.O) (D.ps i g)))
      rw [Units.val_pow_eq_pow_val] at this
      rw [map_pow, map_one]
      exact this
    · simpa [Raw.r0, diagRep] using hk.red g i i
    · have h1 := hc g'
      rw [hg', map_pow] at h1
      refine h1.trans ?_
      refine Eq.trans ?_ (hlab.prod_comp _)
      simp [chi]
  have ht : ∀ x g h, (mapRep 𝔞.toK r (x * (g * h))).trace = (mapRep 𝔞.toK r (x * (h * g))).trace := fun x g h => by
    have h1 : ∀ y, (mapRep 𝔞.toK r y).trace = 𝔞.toK (r y).trace := fun y => by simp [Matrix.trace]
    rw [h1, h1, htr, htr]
    simp only [map_mul, mul_comm (D.ps _ g) (D.ps _ h)]
  rintro (h | h)
  · exact con_span (mapRep 𝔞.toK r) (map_mul _) h 1 isUnit_one (by simpa only [one_mul] using ht)
  · refine con_block _ ht (resQ T.F T.g0) ?_ h
    rw [hc]
    refine (separable_prod_X_sub_C_iff.2 fun i j hij => ?_).squarefree
    by_contra hne
    have h1 : 𝔞.a c (chi D T.pr i (resQ T.F T.g0) - chi D T.pr j (resQ T.F T.g0) : c.O) = 0 := by
      rw [map_sub, sub_eq_zero]; exact Subtype.val_injective hij
    refine hok.dist i j hne (Ideal.Quotient.eq.2 fun hu => ?_)
    exact not_isUnit_zero (h1 ▸ hu.map (𝔞.a c))
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.FinalS
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws
open scoped Matrix
namespace UpperTheory.V.Sd.S2
section Alg
variable {k : Type} [Field k]
variable {Γ₀ Γ : Type} [Group Γ₀] [Group Γ]
end Alg
section Norm
variable {l : ℕ} [Fact l.Prime]
end Norm
section Gal
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
variable {D : Raw Ω c} (T : Tower D)
end Gal
def Final_s : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (D : Raw Ω c) (T : Tower D)
    (ι : Qbar l ≃+* ℂ) (P : PD T.ι (G T.F Ω) (Qbar l)), GlobOk T P.r → LocOk T P → T.IsSeedAlt ι P →
    ∃ (c₁ : Coef l) (h : c.O ≤ c₁.O) (Q : PD T.ι (G T.F Ω) c₁.O), T.SeedPairAlt ι h Q ∧
      Fr.InV (Φ := T.fr ∅) (Q.map (residue c₁.O)) ∧
      (Ent (Q.map (residue c₁.O)).r (-wAl) ∨ (Ent (Q.map (residue c₁.O)).r wBe ∧ Ent (Q.map (residue c₁.O)).r (-wTh)))
end UpperTheory.V.Sd.S2
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.FrobOfProps
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open _root_.GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
open UpperTheory.Zero.LLC UpperTheory.V.Z.Win
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Af.ExLib
namespace UpperTheory.Gal.SV
theorem frob_of_props_alt (P : _root_.UpperTheory.V.Af.Hypotheses') {K Ω : Type} [Field K] [NumberField K] [IsCMField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    {l : ℕ} [Fact l.Prime] {n : ℕ} (hn : 1 ≤ n) {ι : Qbar l ≃+* ℂ} {R : G K Ω →* GL (Fin n) (Qbar l)} {π : CuspSub K n}
    {wt : ℤ} {HT : (K →+* Qbar l) → Multiset ℤ} (H : UpperTheory.GalStar.PropsB (fun h rc => IsRecT h rc) π ι R wt HT) (w : HeightOneSpectrum (𝓞 K))
    (hw : ((l : ℕ) : 𝓞 K) ∉ w.asIdeal) (B : Multiset ℂˣ) (hB : (CG.mk π).HasSat w B) : FrobEig ι R w (algSat n (normV w) B) := by
  obtain ⟨⟨σ, hσ⟩, hi⟩ := _root_.UpperTheory.V.Af.local_comp_complex_of_printed_results P K n π w
  have hS := ((_root_.UpperTheory.V.Af.satake_local_of_printed_results P K n w σ).2 _ π.finPart (hi σ hσ) B).1 hB
  refine frob_of hw σ hS fun A h rc hrc => ?_
  have g := gdOf K Ω A w h rc hrc n σ ((plainOf K n hn π w).2 ⟨_, hB⟩ σ hσ)
  rw [← (H.away w hw A h rc hrc σ hσ).tor g.1 g.2]
  exact isWDOf_wdOf (h := h) hw ι (Units.continuous_val.comp H.cont)
theorem exCS_of_prints :
    _root_.UpperTheory.V.Af.Hypotheses' → ExCS := by
  intro P K Ω _ _ _ _ _ _ l _ ι n hn π χ hreg hsign hd
  have hsign_pow : ∃ m : ℕ, ∀ v, χ.locInf v (-1) = (-1) ^ m := by
    obtain ⟨v₀⟩ : Nonempty (InfinitePlace (maximalRealSubfield K)) := inferInstance
    have hsq : ((χ.locInf v₀ (-1) : ℂˣ) : ℂ) ^ 2 = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← map_pow, neg_one_sq, map_one, Units.val_one]
    rcases sq_eq_one_iff.1 hsq with e | e
    · exact ⟨0, fun v => (hsign v v₀).trans (Units.ext (by simpa using e))⟩
    · exact ⟨1, fun v => (hsign v v₀).trans (Units.ext (by simpa using e))⟩
  obtain ⟨m, hm⟩ := hsign_pow
  have hN : compNorm K (χ * quadChar K ^ (m + n)) = compNorm K χ := by
    rw [map_mul, map_pow, compNorm_quadChar, one_pow, mul_one]
  have hpol : GlobalTheory.ContraPair.PolarizedPair π (χ * quadChar K ^ (m + n)) :=
    ⟨fun v => by
      change χ.locInf v (-1) * (quadChar K ^ (m + n)).locInf v (-1) = (-1) ^ n
      rw [locInf_pow, hm, quadChar_locInf, ← pow_add, ← add_assoc, pow_add, ← two_mul, pow_mul]
      simp, hN ▸ hd⟩
  obtain ⟨R, wt, HT, H⟩ := rowB (_root_.UpperTheory.Gal.SV.rowOf' P.litN.aut.gal) K Ω l ι n hn π _ hreg hpol
  have hsat : ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite, ∃ B, (CG.mk π).HasSat w B :=
    ExLib.eventually_sat (_root_.UpperTheory.V.Af.satake_local_of_printed_results P) π.finPart π.isSmooth_finPart fun w =>
      let ⟨⟨σ, hσ⟩, hi⟩ := _root_.UpperTheory.V.Af.local_comp_complex_of_printed_results P K n π w
      ⟨σ, hi σ hσ⟩
  refine ⟨_, R, wt, HT, hN, H, ⟨H.ss, (hsat.and (eventually_not_mem K l)).mono ?_⟩, fun r hr ha => ?_⟩
  · rintro w ⟨⟨B, hB⟩, hw⟩
    exact ⟨B, hB, _root_.UpperTheory.Gal.SV.frob_of_props_alt P hn H w hw B hB⟩
  · refine propsB_iso H ha.1
      (_root_.UpperTheory.V.Af.iso_of_frobenius_of_printed_results P K Ω l ι n R r H.cont hr H.ss ha.1 ((ha.2.and (eventually_not_mem K l)).mono ?_))
    rintro w ⟨⟨B, h1, h2⟩, hw⟩
    exact ⟨_, _root_.UpperTheory.Gal.SV.frob_of_props_alt P hn H w hw B h1, h2⟩
end UpperTheory.Gal.SV
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LevelZeroEqMaximalCompactBis
section
noncomputable abbrev UpperTheory.V.Z.Win.WitA.weak_admissible_iso := @UpperTheory.V.Z.Win.WitA.iso
end

