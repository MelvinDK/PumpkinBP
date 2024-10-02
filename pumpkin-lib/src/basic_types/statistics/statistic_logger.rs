use std::fmt::Display;

use crate::statistics::log_statistic;

#[derive(Debug)]
pub struct StatisticLogger {
    name_prefix: String,
}

impl StatisticLogger {
    pub(crate) fn new(name_prefix: impl Display) -> Self {
        Self {
            name_prefix: name_prefix.to_string(),
        }
    }

    /// Logs the statistic with the provided `name` and `value`.
    #[allow(unused)]
    pub(crate) fn log_statistic(&self, name: impl Display, value: impl Display) {
        log_statistic(format!("{}{name}", self.name_prefix), value);
    }
}
