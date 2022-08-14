use std::marker::PhantomData;

use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Layouter, floor_planner::V1, Value},
    plonk::*,
    poly::Rotation,
};

#[derive(Debug, Clone)]
pub struct VanillaHoldemConfig {
    pub q_straight: Selector,
    pub q_flush: Selector,
    pub q_one_pair: Selector,
    pub q_two_pair: Selector,
    pub q_three_of_a_kind: Selector,
    pub q_four_of_a_kind: Selector,
    pub cards: [Column<Advice>; 5],
    pub table_cards: [Column<Instance>; 2],
}

struct VanillaHoldemChip<F: FieldExt> {
    config: VanillaHoldemConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> VanillaHoldemChip<F> {
    pub fn construct(config: VanillaHoldemConfig) -> Self {
        Self { config, _marker: PhantomData }
    }
    pub fn configure(meta: &mut ConstraintSystem<F>,
        q_flush: Selector,
        q_straight: Selector,
        q_one_pair: Selector,
        q_two_pair: Selector,
        q_three_of_a_kind: Selector,
        q_four_of_a_kind: Selector,
        cards: [Column<Advice>; 5],
        table_cards: [Column<Instance>; 2],
        num_of_pair: Column<Advice>,
        num_of_same_kind: Column<Advice>,
    ) -> VanillaHoldemConfig {
        meta.create_gate("straight", |meta| {
            let q_straight = meta.query_selector(q_straight);
            let mut constraints = vec![];

            for i in 1..5 {
                // fix rotation
                let diff = meta.query_advice(cards[i], Rotation::cur());

                constraints.push(q_straight.clone() * (diff.clone() - Expression::Constant(F::one())));
            }
            
            constraints
        });

        meta.create_gate("flush", |meta| {
            let q_flush = meta.query_selector(q_flush);
            let mut constraints = vec![];
            
            for i in 0..4 {
                // fix rotation
                let cur = meta.query_advice(cards[i], Rotation::cur());
                let next = meta.query_advice(cards[i + 1], Rotation::cur());

                let diff = cur - next;
                constraints.push(q_flush.clone() * diff);
            }
            constraints
        });

        meta.create_gate("one pair", |meta| {
            let q_one_pair = meta.query_selector(q_one_pair);

            let mut constraints = vec![];
            let num_of_pair = meta.query_advice(num_of_pair, Rotation::cur());

            constraints.push(q_one_pair * (Expression::Constant(F::one()) - num_of_pair));

            constraints
        });

        meta.create_gate("two pair", |meta| {
            let q_two_pair = meta.query_selector(q_two_pair);

            let mut constraints = vec![];
            let num_of_pair = meta.query_advice(num_of_pair, Rotation::cur());

            constraints.push(q_two_pair * (Expression::Constant(F::from_u128(2)) - num_of_pair));

            constraints
        });

        meta.create_gate("three of a kind", |meta| {
            let q_three_of_a_kind = meta.query_selector(q_three_of_a_kind);

            let mut constraints = vec![];
            let num_of_same_kind = meta.query_advice(num_of_same_kind, Rotation::cur());

            constraints.push(q_three_of_a_kind * (Expression::Constant(F::from_u128(3)) - num_of_same_kind));

            constraints
        });

        meta.create_gate("four of a kind", |meta| {
            let q_four_of_a_kind = meta.query_selector(q_four_of_a_kind);

            let mut constraints = vec![];
            let num_of_same_kind = meta.query_advice(num_of_same_kind, Rotation::cur());

            constraints.push(q_four_of_a_kind * (Expression::Constant(F::from_u128(4)) - num_of_same_kind));
        
            constraints
        });

        meta.create_gate("full house", |meta| {
            let q_pair = meta.query_selector(q_one_pair);
            let q_three = meta.query_selector(q_three_of_a_kind);

            let num_of_same_kind = meta.query_advice(num_of_same_kind, Rotation::cur());
            let num_of_pair = meta.query_advice(num_of_pair, Rotation::cur());

            let mut constraints = vec![];
            constraints.push(q_three * (Expression::Constant(F::from_u128(3)) - num_of_same_kind));
            constraints.push(q_pair * (Expression::Constant(F::one()) - num_of_pair));

            constraints
        });

        VanillaHoldemConfig { 
            q_straight,
            q_flush,
            q_one_pair,
            q_two_pair,
            q_three_of_a_kind,
            q_four_of_a_kind,
            cards,
            table_cards,
        }
    }

    pub fn assign_card(
        &self,
        mut layouter: impl Layouter<F>,
        cards: [Value<Assigned<F>>; 2],
        table_cards: [Value<Assigned<F>>; 3],
    ) -> Result<(), Error> {
        let hand: Vec<Value<Assigned<F>>> = cards.iter().chain(table_cards.iter()).map(|v| *v).collect();
        let hand: [Value<Assigned<F>>; 5] = hand.try_into().unwrap();

        layouter.assign_region(
            || "hand check",
            |mut region| {
                for i in 0..5 {
                    region.assign_advice(|| "cards", self.config.cards[i], 0, || hand[i])?;
                }
                
                Ok(())
            }
        )
    }
}

#[derive(Default, Clone)]
pub struct VanillaHoldemCircuit<F: FieldExt> {
    pub cards: [Value<Assigned<F>>; 2],
    pub table_cards: [Value<Assigned<F>>; 3],
}

impl<F: FieldExt> Circuit<F> for VanillaHoldemCircuit<F> {
    type Config = VanillaHoldemConfig;
    type FloorPlanner = V1;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let q_flush = meta.selector();
        let q_straight = meta.selector();
        let q_one_pair = meta.selector();
        let q_two_pair = meta.selector();
        let q_three_of_a_kind = meta.selector();
        let q_four_of_a_kind = meta.selector();

        let cards = [
            meta.advice_column(),
            meta.advice_column(),
            meta.advice_column(),
            meta.advice_column(),
            meta.advice_column(),
        ];
        let table_cards = [
            meta.instance_column(),
            meta.instance_column(),
        ];
        let num_of_pair = meta.advice_column();
        let num_of_same_kind = meta.advice_column();

        VanillaHoldemChip::configure(meta,
            q_flush,
            q_straight,
            q_one_pair,
            q_two_pair,
            q_three_of_a_kind,
            q_four_of_a_kind,
            cards,
            table_cards,
            num_of_pair,
            num_of_same_kind,
        )
    }

    fn synthesize(&self, config: Self::Config, mut layouter: impl Layouter<F>,) -> Result<(), Error> {
        let chip = VanillaHoldemChip::construct(config);

        chip.assign_card(
            layouter.namespace(|| "one hand"),
            self.cards,
            self.table_cards,
        )?;

        Ok(())
    }
}
